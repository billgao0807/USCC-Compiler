include ./Makefile.variables

# Build uscc compiler
all:
	$(MAKE) -C parse all
	$(MAKE) -C opt all
	$(MAKE) -C scan all
	$(MAKE) -C uscc all

# Build dependencies for source files
depend: 
	$(MAKE) -C parse depend
	$(MAKE) -C opt depend
	$(MAKE) -C scan depend
	$(MAKE) -C uscc depend

clean:
	$(MAKE) -C parse clean
	$(MAKE) -C opt clean
	$(MAKE) -C scan clean
	$(MAKE) -C uscc clean
