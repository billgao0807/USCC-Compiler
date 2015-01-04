.SUFFIXES: .cpp .o

include ../Makefile.variables

INCPATH =  -I../../llvm/include
INCPATH += -I../parse

LIBPATH = -L../../lib 
LIBS = ../parse/libparse.a ../opt/libopt.a ../scan/libscan.a

OBJS = main.o 

SRCS = $(OBJS:.o=.cpp) 

CXXFLAGS += $(INCPATH)

ifdef DEBUG
CXXFLAGS += -g 
endif

all: $(EXEC)

$(EXEC): $(OBJS) $(LIBS)
	-@mkdir -p ../bin
	$(CXX) -o ../bin/$(EXEC) $(OBJS) $(LIBS) $(LIBPATH) $(LDFLAGS) 

depend:	
	touch uscc.depend
	makedepend -- $(CXXFLAGS) -- $(SRCS) -f uscc.depend

clean:
	-@rm -f $(OBJS) *.depend*
	-@rm -f ../bin/$(EXEC)

-include ./uscc.depend
