//
//  Emitter.cpp
//  uscc
//
//  Implements helper classes related to LLVM IR
//  construction.
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


#include "Emitter.h"
#include "Parse.h"

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wconversion"
#include <llvm/IR/Value.h>
#include <llvm/PassManager.h>
#include <llvm/IR/IRPrintingPasses.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Bitcode/BitcodeWriterPass.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Verifier.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/LoopPass.h>
#include <llvm/Support/FormattedStream.h>
#include <llvm/Support/Host.h>
#include <llvm/Support/TargetRegistry.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Target/TargetLibraryInfo.h>
#include <llvm/Target/TargetMachine.h>
#include <llvm/Support//FileSystem.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/MC/SubtargetFeature.h>
#include <llvm/IR/Module.h>
#include "../opt/Passes.h"
#pragma clang diagnostic pop

using namespace uscc::parse;
using namespace llvm;

extern size_t NUM_COLORS;

CodeContext::CodeContext(StringTable& strings)
: mGlobal(getGlobalContext())
, mModule(nullptr)
, mBlock(nullptr)
, mStrings(strings)
, mPrintfIdent(nullptr)
, mZero(nullptr)
, mFunc(nullptr)
{
	
}

Emitter::Emitter(Parser& parser) noexcept
: mContext(parser.mStrings)
{
	if (parser.mNeedPrintf)
	{
		mContext.mPrintfIdent = parser.mSymbols.getIdentifier("printf");
	}
	
	// Initialize zero
	mContext.mZero = Constant::getNullValue(IntegerType::getInt32Ty(mContext.mGlobal));
	
	// This is what kicks off the generation of the LLVM IR from the AST
	parser.mRoot->emitIR(mContext);
}

void Emitter::optimize() noexcept
{
	legacy::PassManager pm;
	uscc::opt::registerOptPasses(pm);
	pm.run(*mContext.mModule);
}

void Emitter::print() noexcept
{
	legacy::PassManager pm;
	pm.add(createPrintModulePass(outs()));
	pm.run(*mContext.mModule);
}

void Emitter::writeBitcode(const char* fileName) noexcept
{
	legacy::PassManager pm;
	std::string err;
	raw_fd_ostream file(fileName, err, sys::fs::F_None);
	pm.add(createBitcodeWriterPass(file));
	pm.run(*mContext.mModule);
}

bool Emitter::verify() noexcept
{
	return !verifyModule(*mContext.mModule);
}

// This function will take the bitcode emitted by uscc and convert it to assembly
bool Emitter::writeAsm(const char *fileName, unsigned long numColors) noexcept
{
	NUM_COLORS = static_cast<size_t>(numColors);
	Module* mod = mContext.mModule;
	// This code is copied over from llc
	InitializeNativeTarget();
	InitializeNativeTargetAsmPrinter();
	InitializeNativeTargetAsmParser();
	
	PassRegistry *Registry = PassRegistry::getPassRegistry();
	initializeCore(*Registry);
	initializeCodeGen(*Registry);
	initializeLoopStrengthReducePass(*Registry);
	initializeLowerIntrinsicsPass(*Registry);
	initializeUnreachableBlockElimPass(*Registry);
	
	const char* argv[] = {
		fileName,
		"-optimize-regalloc=true",
		"-regalloc=uscc"
	};
	cl::ParseCommandLineOptions(3, argv, "llvm system compiler\n");
	
	Triple TheTriple;
	TheTriple.setTriple(sys::getDefaultTargetTriple());
	
	auto MCPU = sys::getHostCPUName();
	
	// Get the target specific parser.
	std::string Error;
	const Target *TheTarget = TargetRegistry::lookupTarget("", TheTriple,
														   Error);
	if (!TheTarget) {
		errs() << fileName << ": " << Error;
		return false;
	}
	
	// Package up features to be passed to target/subtarget
	CodeGenOpt::Level OLvl = CodeGenOpt::Less;
	
	TargetOptions Options;
	Options.DisableIntegratedAS = false;
	Options.MCOptions.ShowMCEncoding = false;
	Options.MCOptions.MCUseDwarfDirectory = false;
	Options.MCOptions.AsmVerbose = true;
	
	std::unique_ptr<TargetMachine> target(
										  TheTarget->createTargetMachine(TheTriple.getTriple(), MCPU, "",
																		 Options, Reloc::Default,
																		 CodeModel::Default, OLvl));
	assert(target.get() && "Could not allocate target machine!");
	
	
	assert(mod && "Should have exited if we didn't have a module!");
	TargetMachine &Target = *target.get();
	
	
	sys::fs::OpenFlags OpenFlags = sys::fs::F_None;
	OpenFlags |= sys::fs::F_Text;
	tool_output_file *FDOut = new tool_output_file(fileName, Error,
												   OpenFlags);
	// Figure out where we are going to send the output.
	std::unique_ptr<tool_output_file> Out(FDOut);
	if (!Out) return 1;
	
	// Build up all of the passes that we want to do to the module.
	PassManager PM;
	
	// Add an appropriate TargetLibraryInfo pass for the module's triple.
	TargetLibraryInfo *TLI = new TargetLibraryInfo(TheTriple);
	PM.add(TLI);
		
	// Add the target data from the target machine, if it exists, or the module.
	if (const DataLayout *DL = Target.getDataLayout())
		mod->setDataLayout(DL);
	
	PM.add(new DataLayoutPass(mod));
		
	{
		formatted_raw_ostream FOS(Out->os());
		
		
		// Ask the target to add backend passes as necessary.
		if (Target.addPassesToEmitFile(PM, FOS, TargetMachine::CGFT_AssemblyFile, false,
									   nullptr, nullptr)) {
			errs() << fileName << ": target does not support generation of this"
			<< " file type!\n";
			return 1;
		}
		
		PM.run(*mod);
	}
	
	// Declare success.
	Out->keep();

	return true;
}
