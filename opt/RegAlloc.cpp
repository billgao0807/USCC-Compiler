//
//  RegAlloc.cpp
//  uscc
//
//  Implements a register allocator based on the
//  RegAllocBasic allocator from LLVM.
//---------------------------------------------------------
//  Portions of the code in this file are:
//  Copyright (c) 2003-2014 University of Illinois at
//  Urbana-Champaign.
//  All rights reserved.
//
//  Distributed under the University of Illinois Open Source
//  License.
//---------------------------------------------------------
//  Remaining code is:
//---------------------------------------------------------
//  Copyright (c) 2014, Sanjay Madhav
//  All rights reserved.
//
//  This file is distributed under the BSD license.
//  See LICENSE.TXT for details.
//---------------------------------------------------------

#include "llvm/CodeGen/Passes.h"
#include "../lib/CodeGen/AllocationOrder.h"
#include "../lib/CodeGen/LiveDebugVariables.h"
#include "../lib/CodeGen/RegAllocBase.h"
#include "../lib/CodeGen/Spiller.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/CodeGen/CalcSpillWeights.h"
#include "llvm/CodeGen/LiveIntervalAnalysis.h"
#include "llvm/CodeGen/LiveRangeEdit.h"
#include "llvm/CodeGen/LiveRegMatrix.h"
#include "llvm/CodeGen/LiveStackAnalysis.h"
#include "llvm/CodeGen/MachineBlockFrequencyInfo.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineLoopInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/RegAllocRegistry.h"
#include "llvm/CodeGen/VirtRegMap.h"
#include "llvm/PassAnalysisSupport.h"
#undef DEBUG
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetRegisterInfo.h"
#include <cstdlib>
#include <queue>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <iostream>
#include <algorithm>
#include <map>

using namespace llvm;

#define DEBUG_TYPE "regalloc"

static FunctionPass* createUSCCRegisterAllocator();

static RegisterRegAlloc usccRegAlloc("uscc", "USCC register allocator",
                                     createUSCCRegisterAllocator);

size_t NUM_COLORS = 4;

namespace {
    std::map<LiveInterval*,int> stackMap;
    struct CompSpillWeight {
        bool operator()(LiveInterval *A, LiveInterval *B) const {
//            return A->weight < B->weight;
            return stackMap[A] < stackMap[B];
        }
    };
}

namespace {
    // PA6: Add any global members needed
    std::vector<LiveInterval*> liveIntervals;
    class Graph {
    private:
        
        int vertexCount;
        bool* presentArray;
    public:
        bool** adjacencyMatrix;
        Graph(int vertexCount) {
            this->vertexCount = vertexCount;
            adjacencyMatrix = new bool*[vertexCount];
            presentArray = new bool[vertexCount];
            for (int i = 0; i < vertexCount; i++) {
                adjacencyMatrix[i] = new bool[vertexCount];
                presentArray[i] = true;
                for (int j = 0; j < vertexCount; j++)
                    adjacencyMatrix[i][j] = false;
            }
        }
        
        void addEdge(int i, int j) {
            if (i >= 0 && i < vertexCount && j >= 0 && j < vertexCount && i != j) {
                adjacencyMatrix[i][j] = true;
                adjacencyMatrix[j][i] = true;
            }
        }
        
        void removeEdge(int i, int j) {
            if (i!= j && i >= 0 && i < vertexCount && j >= 0 && j < vertexCount) {
                adjacencyMatrix[i][j] = false;
                adjacencyMatrix[j][i] = false;
            }
        }
        
        void removeNode(int node) {
            presentArray[node] = false;
            for (int j = 0; j < liveIntervals.size(); j++) {
                if (adjacencyMatrix[node][j]) {
                    removeEdge(node, j);
                }
            }
        }
        
        bool isEdge(int i, int j) {
            if (i >= 0 && i < vertexCount && j > 0 && j < vertexCount)
                return adjacencyMatrix[i][j];
            else
                return false;
        }
        
        int getNumOfEdges(int node) {
            
            int count = 0;
            for (int i = 0; i < vertexCount; i++)
                if (adjacencyMatrix[node][i])
                    count++;
            return count;

        }
        
        bool empty() {
            for (int i = 0; i < vertexCount; i++) {
//                for (int j = 0; j < vertexCount; j++)
                    if (presentArray[i]) {
                        return false;
                    }
            }
            return true;
        }
        
        bool nodePresent(int node) {
            return presentArray[node];
        }
        
        void print() {
            std::cout << "  ";
            for (int i = 0; i < vertexCount; i++) {
                if (i < 9) {
                    std::cout << " ";
                }
                std::cout << i+1 << " ";
            }
            std::cout << "\n";
            for (int i = 0; i < vertexCount; i++) {
                std::cout << i+1;
                if (i < 9) {
                    std::cout << " ";
                }
                for (int j = 0; j < vertexCount; j++) {
                    if (adjacencyMatrix[i][j]) std::cout << " * ";
                    else std::cout << " - ";
                }
                std::cout << "\n";
            }
        }
        
        ~Graph() {
            for (int i = 0; i < vertexCount; i++)
                delete[] adjacencyMatrix[i];
            delete[] adjacencyMatrix;
        }
    };
    
    
    /// RAUSCC allocator pass
    class RAUSCC : public MachineFunctionPass, public RegAllocBase {
        // context
        MachineFunction *MF;
        
        Graph* graph;
        
        // state
        std::unique_ptr<Spiller> SpillerInstance;
        std::priority_queue<LiveInterval*, std::vector<LiveInterval*>,
        CompSpillWeight> Queue;
        
        // Scratch space.  Allocated here to avoid repeated malloc calls in
        // selectOrSplit().
        BitVector UsableRegs;
        
    public:
        RAUSCC();
        
        /// Return the pass name.
        const char* getPassName() const override {
            return "Basic Register Allocator";
        }
        
        /// RAUSCC analysis usage.
        void getAnalysisUsage(AnalysisUsage &AU) const override;
        
        void releaseMemory() override;
        
        Spiller &spiller() override { return *SpillerInstance; }
        
        void enqueue(LiveInterval *LI) override {
            Queue.push(LI);
        }
        
        LiveInterval *dequeue() override {
            if (Queue.empty())
                return nullptr;
            LiveInterval *LI = Queue.top();
            Queue.pop();
            return LI;
        }
        
        unsigned selectOrSplit(LiveInterval &VirtReg,
                               SmallVectorImpl<unsigned> &SplitVRegs) override;
        
        /// Perform register allocation.
        bool runOnMachineFunction(MachineFunction &mf) override;
        
        // Helper for spilling all live virtual registers currently unified under preg
        // that interfere with the most recently queried lvr.  Return true if spilling
        // was successful, and append any new spilled/split intervals to splitLVRs.
        bool spillInterferences(LiveInterval &VirtReg, unsigned PhysReg,
                                SmallVectorImpl<unsigned> &SplitVRegs);
        
        void initGraph();
        void simplifyGraph();
        static char ID;
        
        bool checkTrivialAndPush(int &index, int&);
    };
    
    char RAUSCC::ID = 0;
    
} // end anonymous namespace

RAUSCC::RAUSCC(): MachineFunctionPass(ID) {
    initializeLiveDebugVariablesPass(*PassRegistry::getPassRegistry());
    initializeLiveIntervalsPass(*PassRegistry::getPassRegistry());
    initializeSlotIndexesPass(*PassRegistry::getPassRegistry());
    initializeRegisterCoalescerPass(*PassRegistry::getPassRegistry());
    initializeMachineSchedulerPass(*PassRegistry::getPassRegistry());
    initializeLiveStacksPass(*PassRegistry::getPassRegistry());
    initializeMachineDominatorTreePass(*PassRegistry::getPassRegistry());
    initializeMachineLoopInfoPass(*PassRegistry::getPassRegistry());
    initializeVirtRegMapPass(*PassRegistry::getPassRegistry());
    initializeLiveRegMatrixPass(*PassRegistry::getPassRegistry());
}

void RAUSCC::getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesCFG();
    AU.addRequired<AliasAnalysis>();
    AU.addPreserved<AliasAnalysis>();
    AU.addRequired<LiveIntervals>();
    AU.addPreserved<LiveIntervals>();
    AU.addPreserved<SlotIndexes>();
    AU.addRequired<LiveDebugVariables>();
    AU.addPreserved<LiveDebugVariables>();
    AU.addRequired<LiveStacks>();
    AU.addPreserved<LiveStacks>();
    AU.addRequired<MachineBlockFrequencyInfo>();
    AU.addPreserved<MachineBlockFrequencyInfo>();
    AU.addRequiredID(MachineDominatorsID);
    AU.addPreservedID(MachineDominatorsID);
    AU.addRequired<MachineLoopInfo>();
    AU.addPreserved<MachineLoopInfo>();
    AU.addRequired<VirtRegMap>();
    AU.addPreserved<VirtRegMap>();
    AU.addRequired<LiveRegMatrix>();
    AU.addPreserved<LiveRegMatrix>();
    MachineFunctionPass::getAnalysisUsage(AU);
}

void RAUSCC::releaseMemory() {
    SpillerInstance.reset();
    
    // PA6: Delete any member data stored for each function
//    free(graph);
    liveIntervals.clear();
    stackMap.clear();
}


// Spill or split all live virtual registers currently unified under PhysReg
// that interfere with VirtReg. The newly spilled or split live intervals are
// returned by appending them to SplitVRegs.
bool RAUSCC::spillInterferences(LiveInterval &VirtReg, unsigned PhysReg,
                                SmallVectorImpl<unsigned> &SplitVRegs) {
    // Record each interference and determine if all are spillable before mutating
    // either the union or live intervals.
    SmallVector<LiveInterval*, 8> Intfs;
    
    // Collect interferences assigned to any alias of the physical register.
    for (MCRegUnitIterator Units(PhysReg, TRI); Units.isValid(); ++Units) {
        LiveIntervalUnion::Query &Q = Matrix->query(VirtReg, *Units);
        Q.collectInterferingVRegs();
        if (Q.seenUnspillableVReg())
            return false;
        for (unsigned i = Q.interferingVRegs().size(); i; --i) {
            LiveInterval *Intf = Q.interferingVRegs()[i - 1];
            if (!Intf->isSpillable() || Intf->weight > VirtReg.weight)
                return false;
            Intfs.push_back(Intf);
        }
    }
    DEBUG(dbgs() << "spilling " << TRI->getName(PhysReg) <<
          " interferences with " << VirtReg << "\n");
    assert(!Intfs.empty() && "expected interference");
    std::cout << "Spilling "; std::cout.flush(); VirtReg.dump();
    // Spill each interfering vreg allocated to PhysReg or an alias.
    for (unsigned i = 0, e = Intfs.size(); i != e; ++i) {
        LiveInterval &Spill = *Intfs[i];
        
        // Skip duplicates.
        if (!VRM->hasPhys(Spill.reg))
            continue;
        
        // Deallocate the interfering vreg by removing it from the union.
        // A LiveInterval instance may not be in a union during modification!
        Matrix->unassign(Spill);
        
        // Spill the extracted interval.
        LiveRangeEdit LRE(&Spill, SplitVRegs, *MF, *LIS, VRM);
        spiller().spill(LRE);
    }
    return true;
}

// Driver for the register assignment and splitting heuristics.
// Manages iteration over the LiveIntervalUnions.
//
// This is a minimal implementation of register assignment and splitting that
// spills whenever we run out of registers.
//
// selectOrSplit can only be called once per live virtual register. We then do a
// single interference test for each register the correct class until we find an
// available register. So, the number of interference tests in the worst case is
// |vregs| * |machineregs|. And since the number of interference tests is
// minimal, there is no value in caching them outside the scope of
// selectOrSplit().
unsigned RAUSCC::selectOrSplit(LiveInterval &VirtReg,
                               SmallVectorImpl<unsigned> &SplitVRegs) {
    // Populate a list of physical register spill candidates.
    SmallVector<unsigned, 8> PhysRegSpillCands;
    
    // Check for an available register in this class.
    AllocationOrder Order(VirtReg.reg, *VRM, RegClassInfo);
    while (unsigned PhysReg = Order.next()) {
        // Check for interference in PhysReg
        switch (Matrix->checkInterference(VirtReg, PhysReg)) {
            case LiveRegMatrix::IK_Free:
                // PhysReg is available, allocate it.
                std::cout << "Assigning to physical register: "; std::cout.flush(); VirtReg.dump();
                return PhysReg;
                
            case LiveRegMatrix::IK_VirtReg:
                // Only virtual registers in the way, we may be able to spill them.
                PhysRegSpillCands.push_back(PhysReg);
                continue;
                
            default:
                // RegMask or RegUnit interference.
                continue;
        }
    }
    
    // Try to spill another interfering reg with less spill weight.
    for (SmallVectorImpl<unsigned>::iterator PhysRegI = PhysRegSpillCands.begin(),
         PhysRegE = PhysRegSpillCands.end(); PhysRegI != PhysRegE; ++PhysRegI) {
        if (!spillInterferences(VirtReg, *PhysRegI, SplitVRegs))
            continue;
        
        assert(!Matrix->checkInterference(VirtReg, *PhysRegI) &&
               "Interference after spill.");
        // Tell the caller to allocate to this newly freed physical register.
        return *PhysRegI;
    }
    
    // No other spill candidates were found, so spill the current VirtReg.
    DEBUG(dbgs() << "spilling: " << VirtReg << '\n');
    std::cout << "Spilling "; std::cout.flush(); VirtReg.dump();
    if (!VirtReg.isSpillable())
        return ~0u;
    LiveRangeEdit LRE(&VirtReg, SplitVRegs, *MF, *LIS, VRM);
    spiller().spill(LRE);
    
    // The live virtual register requesting allocation was spilled, so tell
    // the caller not to allocate anything during this round.
    return 0;
}

bool RAUSCC::runOnMachineFunction(MachineFunction &mf) {
    DEBUG(dbgs() << "********** USCC REGISTER ALLOCATION **********\n"
          << "********** Function: "
          << mf.getName() << '\n');
    std::cout << "********** USCC REGISTER ALLOCATION **********\n";
    std::string funcName(mf.getName());
    std::cout << "********** Function: " << funcName << '\n';
    std::cout << "NUM_COLORS=" << NUM_COLORS << '\n';
    MF = &mf;
    RegAllocBase::init(getAnalysis<VirtRegMap>(),
                       getAnalysis<LiveIntervals>(),
                       getAnalysis<LiveRegMatrix>());
    
    calculateSpillWeightsAndHints(*LIS, *MF,
                                  getAnalysis<MachineLoopInfo>(),
                                  getAnalysis<MachineBlockFrequencyInfo>());
    
    SpillerInstance.reset(createInlineSpiller(*this, *MF, *VRM));
    initGraph();
    simplifyGraph();
    
    allocatePhysRegs();
    
    // Diagnostic output before rewriting
    DEBUG(dbgs() << "Post alloc VirtRegMap:\n" << *VRM << "\n");
    
    releaseMemory();
    return true;
}

// Build an interference graph
void RAUSCC::initGraph() {
    // PA6: Implement
    
    for (unsigned i = 0, e = MRI->getNumVirtRegs(); i != e; ++i) {
        // reg ID
        unsigned Reg = TargetRegisterInfo::index2VirtReg(i);
        // if is not a DEBUG register
        if (MRI->reg_nodbg_empty(Reg))
            continue;
        // get the respective LiveInterval
        LiveInterval *VirtReg = &LIS->getInterval(Reg);
        liveIntervals.push_back(VirtReg);
    }
    graph = new Graph(liveIntervals.size());
    for (int i = 0; i < liveIntervals.size(); i++) {
        for (int j = 0; j < i; j++) {
            if (i != j && liveIntervals[i]->overlaps(*(liveIntervals[j]))) {
//                std::cout << "Adding edge from " << i + 1 << " " << j + 1 << " ";
//                liveIntervals[i]->dump();
//                std::cout << " to ";
//                liveIntervals[j]->dump();
                //                std::cout << "\n";
                graph->addEdge(i, j);
//                if (graph->adjacencyMatrix[i][j]) {
//                    std::cout << "Added edge from " << i + 1 << " " << j + 1 << " \n";
//                }
//                graph->print();
            }
        }
        
    }
//    std::cout << "InitGraphFinish\n";
}

void RAUSCC::simplifyGraph() {
    // PA6: Implement
    int rmCounter = 0;
    int genCounter = 0;
    while (!graph->empty()) {
        if (!checkTrivialAndPush(genCounter, rmCounter)) {
            
            LiveInterval* spill = NULL;
            int spillIndex = 0;
            for (int j = 0; j < liveIntervals.size(); j++) {
                if (graph->nodePresent(j)) {
                    spill = liveIntervals[j];
                    spillIndex = j;
                    break;
                }
            }
            
            
            for (int j = 0; j < liveIntervals.size(); j++) {
                if (graph->nodePresent(j) && liveIntervals[j]->weight < spill->weight) {
                    spill = liveIntervals[j];
                    spillIndex = j;
                }
            }
            if (spill == NULL) {
                break;
            }
            int numOfNei = graph->getNumOfEdges(spillIndex);
            std::cout << "Spill candidate (neighbors=" << numOfNei << ", weight=" << spill->weight << "):";
            spill->dump();
            stackMap.insert(std::pair<LiveInterval*, int>(spill, genCounter));
            std::cout << "Removal " << rmCounter << ": ";
            spill->dump();
            graph->removeNode(spillIndex);
            rmCounter++;
            genCounter++;
        }
    }
    
}

bool RAUSCC::checkTrivialAndPush (int &index, int &rmCounter) {
    for (int i = 0; i < liveIntervals.size(); i++) {
        if (!graph->nodePresent(i)) {
            continue;
        }
        int numOfNei = graph->getNumOfEdges(i);
        if (numOfNei < NUM_COLORS) {
            std::cout << "Found neighbors=" << numOfNei << " for ";
            liveIntervals[i]->dump();
            stackMap.insert(std::pair<LiveInterval*, int>(liveIntervals[i], index));
            std::cout << "Removal " << rmCounter << ": ";
            liveIntervals[i]->dump();
            graph->removeNode(i);
            index++;
            return true;
        }
    }
    return false;
}


FunctionPass* createUSCCRegisterAllocator() {
    return new RAUSCC();
}
