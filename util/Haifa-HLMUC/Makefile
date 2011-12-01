# Makefile for libhhlmuc
# Created: 2011-12-01 Christoph Sticksel

# This makefile is in the root of the MiniSat directory
export MROOT = $(shell pwd)

# How the library we make is called
export LIB = hhlmuc

# Make a release library version of hhlmuc
all:
	cd $(MROOT)/simp && $(MAKE) libr

.PHONY : clean

# Clean the library here and clean in the MiniSat directories
clean:
	@rm -f lib$(LIB).a lib$(LIB)_release.a
	cd $(MROOT)/simp && $(MAKE) clean
