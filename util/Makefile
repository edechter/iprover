# Makefile for utilities 
# Created: 2011-12-01 Christoph Sticksel

# Use C++ compiler
CXX=g++

# Use native OCaml compiler
OCAMLC=ocamlopt

OCAMLLIBDIR=/usr/lib/ocaml
OCAMLINCDIR=/usr/lib/ocaml

MINISATDIR=$(CURDIR)/minisat
HHLMUCDIR=$(CURDIR)/Haifa-HLMUC

all: hhlmuc minisat

.PHONY : clean

clean: clean-hhlmuc clean-minisat

# Set variables for hhlmuc and clean-hhlmuc
hhlmuc clean-hhlmuc: export LIB = hhlmuc
hhlmuc clean-hhlmuc: export MROOT = $(HHLMUCDIR)

# Set variables for minisat and clean-minisat
minisat clean-minisat: export LIB = minisat
minisat clean-minisat: export MROOT = $(MINISATDIR)

.PHONY : hhlmuc

# Make hhlmuc release library 
hhlmuc:
	cd $(MROOT)/simp && $(MAKE) libr

.PHONY : minisat 

# Make minisat release library 
minisat:
	cd $(MROOT)/simp && $(MAKE) libr

.PHONY : clean-hhlmuc

# Clean hhlmuc
clean-hhlmuc:
	cd $(MROOT)/simp && $(MAKE) clean

.PHONY : clean-minisat

# Clean minisat
clean-minisat:
	cd $(MROOT)/simp && $(MAKE) clean


src/minisat_stubs.o: src/minisat_stubs.cpp minisat
	$(CXX) -c -o $@ -I $(OCAMLINCDIR) -I $(MINISATDIR) $<


src/minisat-test: src/minisat_stubs.o src/minisat.ml
# Must have -cclib -lminisat after src/minisat_stubs.o
	$(OCAMLC) -cc $(CXX) -cclib -I$(CURDIR)/src -cclib -L$(MINISATDIR)/simp -cclib -I$(MINISATDIR) -o $@ $^ -cclib -lminisat
