# Makefile for utilities 
# Created: 2011-12-01 Christoph Sticksel

# Use C++ compiler
CXX=g++

AR=ar
OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLMKLIB=ocamlmklib

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


obj/minisat_stubs.o: src/minisat_stubs.cpp minisat
	$(CXX) -c -o $@ -I $(OCAMLINCDIR) -I $(MINISATDIR) $<

obj/minisat.cmi: src/minisat.mli
	$(OCAMLC) -c -o $@ $<

obj/minisat.cmo:  obj/minisat.cmi src/minisat.ml
	$(OCAMLC) -c -I $(CURDIR)/obj -o $@ $<

obj/minisat.cmx: src/minisat.ml obj/minisat.cmi 
	$(OCAMLOPT) -c -I $(CURDIR)/obj -o $@ $<

# Must have -cclib -lminisat and -cclib -lstdc++ after src/minisat_stubs.o
# lib/minisat.cmxa lib/minisat.cma: obj/minisat.cmx obj/minisat.cmo obj/minisat_stubs.o
#	$(OCAMLMKLIB) -L$(MINISATDIR)/simp -I $(CURDIR)/obj -o lib/minisat $^ -lminisat -lstdc++

lib/minisat.cma: obj/minisat.cmo
	$(OCAMLC) -a -custom -o $@ $< -cclib -lminisat -cclib -lstdc++ -ccopt -L$(MINISATDIR)/simp

lib/minisat.cmxa: obj/minisat.cmx
#	$(OCAMLOPT) -a -o $@ $< -cclib -lminisat -cclib -lstdc++ -ccopt -L$(MINISATDIR)/simp
	$(OCAMLOPT) -a -o $@ $< -cclib -lminisat -cclib -lstdc++ -ccopt -L$(MINISATDIR)/simp

lib/minisat_stubs.a: obj/minisat_stubs.o
	$(AR) rc $@ $<

obj/minisat_test.cmx: src/minisat_test.ml
	$(OCAMLOPT) -c -I $(CURDIR)/obj -o $@ $<

bin/minisat-test: lib/minisat_stubs.a lib/minisat.cmxa obj/minisat_test.cmx
	$(OCAMLOPT) -o $@ $^ -I $(CURDIR)/obj -cclib -L$(MINISATDIR)/simp -cclib -lminisat -cclib -lstdc++

