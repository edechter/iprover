# Makefile for utilities 
# Created: 2011-12-01 Christoph Sticksel

# These variables must be exported to be available in the sub-Makefile
# Makefile.clib

# C++ compiler
export CXX=g++

export AR=ar
export OCAMLC=ocamlc
export OCAMLOPT=ocamlopt
export OCAMLMKLIB=ocamlmklib
export OCAMLMKTOP=ocamlmktop
export RANLIB=ranlib

export OCAMLLIBDIR=/usr/lib/ocaml
export OCAMLINCDIR=/usr/lib/ocaml
# export OCAMLLIBDIR=/home/chris/lib/ocaml
# export OCAMLINCDIR=/home/chris/lib/ocaml
# export OCAMLLIBDIR=/shareddata/homes/sticksec/lib/ocaml
# export OCAMLINCDIR=/shareddata/homes/sticksec/lib/ocaml

MINISATDIR=$(CURDIR)/minisat
HHLMUCDIR=$(CURDIR)/Haifa-HLMUC

all: hhlmuc minisat minisat-ocaml hhlmuc-ocaml

.PHONY : clean

clean: clean-hhlmuc clean-minisat clean-minisat-ocaml

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


minisat-ocaml clean-minisat-ocaml: export CLIBNAME=minisat
minisat-ocaml clean-minisat-ocaml: export CLIBINCDIR=$(MINISATDIR)
minisat-ocaml clean-minisat-ocaml: export CLIBLIBDIR=$(MINISATDIR)/simp

minisat-ocaml: 
	$(MAKE) -f Makefile.clib minisat-ocaml

clean-minisat-ocaml: 
	$(MAKE) -f Makefile.clib clean-minisat-ocaml


hhlmuc-ocaml clean-hhlmuc-ocaml: export CLIBNAME=hhlmuc
hhlmuc-ocaml clean-hhlmuc-ocaml: export CLIBINCDIR=$(HHLMUCDIR)
hhlmuc-ocaml clean-hhlmuc-ocaml: export CLIBLIBDIR=$(HHLMUCDIR)/simp
hhlmuc-ocaml clean-hhlmuc-ocaml: export EXTRACCLIB=-cclib -lz

hhlmuc-ocaml: 
	$(MAKE) -f Makefile.clib hhlmuc-ocaml

clean-hhlmuc-ocaml: 
	$(MAKE) -f Makefile.clib clean-hhlmuc-ocaml
