.SUFFIXES: .cpp .o

include ../Makefile.variables

INCPATH = -I../../llvm/include

OBJS = ASTEmit.o ASTExpr.o ASTNodes.o ASTPrint.o ASTStmt.o Emitter.o Parse.o ParseExcept.o ParseExpr.o ParseStmt.o Symbols.o 

SRCS = $(OBJS:.o=.cpp)

CXXFLAGS += $(INCPATH) 

ifdef DEBUG
CXXFLAGS += -g
endif

all: libparse.a

libparse.a: $(OBJS)
	ar rcs libparse.a $(OBJS)

depend:
	touch libparse.depend
	makedepend -- $(CXXFLAGS) -- $(SRCS) -f libparse.depend

clean:
	-@rm -f $(OBJS) *.depend*
	-@find . -name 'lib*.a' -exec rm {} \;

-include ./libparse.depend
