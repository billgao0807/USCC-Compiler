.SUFFIXES: .cpp .o

include ../Makefile.variables

INCPATH =  -I../../llvm/include

OBJS = FlexLexer.o Tokens.o

SRCS = $(OBJS:.o=.cpp)

CXXFLAGS += $(INCPATH) -Wno-deprecated-register

ifdef DEBUG
CXXFLAGS += -g
endif

all: FlexLexer.cpp libscan.a

FlexLexer.cpp: usc.l
	flex -oFlexLexer.cpp -+ usc.l

libscan.a: $(OBJS)
	ar rcs libscan.a $(OBJS)

depend:
	touch libscan.depend
	makedepend -- $(CXXFLAGS) -- $(SRCS) -f libscan.depend

clean:
	-@rm -f $(OBJS) *.depend* FlexLexer.cpp
	-@find . -name 'lib*.a' -exec rm {} \;

-include ./libscan.depend
