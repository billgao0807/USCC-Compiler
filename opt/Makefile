.SUFFIXES: .cpp .o

include ../Makefile.variables

INCPATH =  -I../../llvm/include
INCPATH += -I../parse

OBJS = ConstantBranch.o ConstantOps.o DeadBlocks.o SSABuilder.o LICM.o Passes.o

SRCS = $(OBJS:.o=.cpp)

CXXFLAGS += $(INCPATH) -fno-rtti 

ifdef DEBUG
CXXFLAGS += -g
endif

all: libopt.a

libopt.a: $(OBJS)
	ar rcs libopt.a $(OBJS)

depend:
	touch libopt.depend
	makedepend -- $(CXXFLAGS) -- $(SRCS) -f libopt.depend

clean:
	-@rm -f $(OBJS) *.depend*
	-@find . -name 'lib*.a' -exec rm {} \;

-include ./libopt.depend
