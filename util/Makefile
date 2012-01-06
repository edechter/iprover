# Makefile for utilities 
# Created: 2011-12-01 Christoph Sticksel

# Use C++ compiler
CXX=g++

AR=ar
OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLMKLIB=ocamlmklib
OCAMLMKTOP=ocamlmktop
RANLIB=ranlib

# OCAMLLIBDIR=/usr/lib/ocaml
# OCAMLINCDIR=/usr/lib/ocaml
OCAMLLIBDIR=/home/chris/lib/ocaml
OCAMLINCDIR=/home/chris/lib/ocaml

MINISATDIR=$(CURDIR)/minisat
HHLMUCDIR=$(CURDIR)/Haifa-HLMUC

all: hhlmuc minisat minisat-ocaml

.PHONY : clean

clean: clean-hhlmuc clean-minisat clean-minisat-lib

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

.PHONY : clean-minisat-lib

clean-minisat-ocaml: 
	rm lib/*
	rm obj/*


# Cannot use minisat, clashes with name of libminisat.a
CLIBNAME=minisat

# Build an interface to a C++ library from the following parts:
# 
# - src/$(OCAMLLIBNAME)_stubs.cpp: Stub code to call the library $(CLIBNAME)
# - src/$(OCAMLLIBNAME).mli: Interface of the OCaml library
# - src/$(OCAMLLIBNAME).ml: Implementation of the OCaml library
#
# Results in 
# 
# - lib/$(OCAMLLIBNAME).cmxa, lib/$(OCAMLLIBNAME)_stubs.a 


.PHONY: $(CLIBNAME)-ocaml

# Build OCaml and C part of the library 
$(CLIBNAME)-ocaml: lib/$(CLIBNAME).cmxa lib/$(CLIBNAME).a

# C object file for stub code 
lib/$(CLIBNAME)_stubs.o: src/$(CLIBNAME)_stubs.cpp
	$(CXX) -c -o $@ -I$(OCAMLINCDIR) -I$(MINISATDIR) $<

# Compiled interface for OCaml
lib/$(CLIBNAME).cmi: src/$(CLIBNAME).mli
	$(OCAMLC) -c -o $@ $<

# Byte-code of implementation 
lib/$(CLIBNAME).cmo: src/$(CLIBNAME).ml lib/$(CLIBNAME).cmi 
	$(OCAMLC) -c -I $(CURDIR)/obj -I $(CURDIR)/lib -o $@ $<

# Native code of implementation 
lib/$(CLIBNAME).cmx lib/$(CLIBNAME).o: src/$(CLIBNAME).ml lib/$(CLIBNAME).cmi 
	$(OCAMLOPT) -c -I $(CURDIR)/lib -o $@ $<

# Pack C code into an archive 
lib/lib$(CLIBNAME)_stubs.a: lib/$(CLIBNAME)_stubs.o
	$(AR) rc $@ $^
	$(RANLIB) $@

# For linking: must have -cclib -lminisat and -cclib -lstdc++ after
# src/minisat_stubs.o

# Pack byte-code OCaml implementation into library 
lib/$(CLIBNAME).cma lib/$(CLIBNAME).a: lib/$(CLIBNAME).cmo lib/lib$(CLIBNAME)_stubs.a 
	$(OCAMLC) -a -custom -I $(CURDIR)/lib -o $@ $< -cclib -L$(CURDIR)/lib -cclib -L$(MINISATDIR)/simp -cclib -l$(CLIBNAME)_stubs -cclib -l$(CLIBNAME) -cclib -lstdc++

# Pack native code OCaml implementation into library 
lib/$(CLIBNAME).cmxa lib/$(CLIBNAME).a: lib/$(CLIBNAME).cmx lib/lib$(CLIBNAME)_stubs.a 
	$(OCAMLOPT) -a -I $(CURDIR)/lib -o $@ $< -cclib -L$(CURDIR)/lib -cclib -L$(MINISATDIR)/simp -cclib -l$(CLIBNAME)_stubs -cclib -l$(CLIBNAME) -cclib -lstdc++

lib/dll$(CLIBNAME).so:
	$(CC) -shared -o $@ -L$(CURDIR)/lib -L$(MINISATDIR)/simp -l$(CLIBNAME)_stubs -l$(CLIBNAME) -lstdc++

$(CLIBNAME)_test.cmo: src/$(CLIBNAME)_test.ml
	$(OCAMLC) -c -I $(CURDIR)/lib -o $@ $^

$(CLIBNAME)_test.cmx: src/$(CLIBNAME)_test.ml
	$(OCAMLOPT) -c -I $(CURDIR)/lib -o $@ $^

$(CLIBNAME)-test: lib/$(CLIBNAME).cmxa $(CLIBNAME)_test.cmx 
	$(OCAMLOPT) -I $(CURDIR)/lib -o $@ $^

$(CLIBNAME)-test-bc: lib/$(CLIBNAME).cma $(CLIBNAME)_test.cmo
	$(OCAMLC) -I $(CURDIR)/lib -o $@ $^

# FIXME: open Minisat;; in resulting toplevel fails
$(CLIBNAME)-top: lib/dll$(CLIBNAME).so lib/$(CLIBNAME).cma
	$(OCAMLMKTOP) -custom -I $(CURDIR)/lib -o $@ $^ -cclib -L$(CURDIR)/lib -cclib -ldll$(CLIBNAME)
