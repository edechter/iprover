# first run "./configure" to create Makefile.extras
# make PROFILE=true for profile 
# make CPP=true for c++ version of minisat
# to archive "make archive"
# to archive E bundle "make E=true archive"

OCAML=ocaml
OCAMLC=ocamlc
OCAMLOPT=ocamlopt
#OCAMLLIB=/usr/local/lib/ocaml
#OCAMLLIB=/usr/lib/ocaml/3.10.2
#OCAMLLIB is set in Make.extras
EPROVER_PATH="./E_Prover" 
OPT=true
OBJPATH=obj/
ADDTONAME=
PROFILE=
OCAMLOPTOPT=ocamlopt.opt
OCAMLDEP=ocamldep
INCLUDES=
#OCAMLFLAGS=$(INCLUDES)
#OCAMLOPTFLAGS=$(INCLUDES)

#CPP=true for CPP solver
CPP=

#different modifications of MiniSat solver
#CSOLVER=solver_mod_inc_clauses 
CSOLVER=solver
#CSOLVER=solver_basic

OCAMLFLAGS=-inline 10 -I obj/ -I util/lib 
#OCAMLFLAGS=-I obj/
#LIB  = lib
LEXER = lexer_tptp
PARSER = parser_tptp
#BEFORE_PARSING = lib parser_types 
#PARSER_TYPES = parser_types
#PARSING= src/$(LEXER).ml src/$(PARSER).ml

include Makefile.extras



#BASE_NAMES = lib options statistics bit_vec tableArray heap priority_queues tree trie trie_func vectorIndex abstDB abstAssignDB symbol symbolDB var term termDB orderings subst substBound dismatching clause selection clauseAssignDB clauseDB parser_types lexer_tptp parser_tptp parsed_input_to_db parseFiles splitting unif unifIndex discrTree subsetSubsume subsumptionIndex eq_axioms propSolver prop_solver_exchange inference_rules model_inst finite_models preprocess prep_sem_filter large_theories

BASE_NAMES_BEFORE_LEXER = lib options statistics bit_vec tableArray heap priority_queues tree trie trie_func vectorIndex abstDB abstAssignDB symbol symbolDB var term termDB orderings subst substBound dismatching clause selection clauseAssignDB clauseDB parser_types

#BASE_NAMES_AFTER_LEXER = parser_tptp parsed_input_to_db parseFiles splitting unif unifIndex discrTree subsetSubsume subsumptionIndex eq_axioms propSolver prop_solver_exchange inference_rules model_inst finite_models preprocess prep_sem_filter large_theories discount instantiation

BASE_NAMES_AFTER_LEXER = parser_tptp parseFiles splitting unif unifIndex discrTree subsetSubsume subsumptionIndex eq_axioms cMinisat propSolver prop_solver_exchange bmc1Axioms inference_rules model_inst finite_models preprocess prep_sem_filter prep_sem_filter_unif large_theories discount instantiation

BASE_NAMES_WITHOUT_LEXER = $(BASE_NAMES_BEFORE_LEXER) $(BASE_NAMES_AFTER_LEXER)
BASE_NAMES_WITH_LEXER = $(BASE_NAMES_BEFORE_LEXER) $(LEXER) $(BASE_NAMES_AFTER_LEXER)

#OBJ_BASE_NAMES = $(BEFORE_PARSING) $(LEXER) $(PARSER) $(BASE_NAMES)
OBJ_BASE_NAMES = $(BASE_NAMES_WITH_LEXER)

#For testing

TEST_NAMES_AFTER_LEXER = parser_tptp 
TEST_NAMES_WITHOUT_LEXER = $(BASE_NAMES_BEFORE_LEXER) $(TEST_NAMES_AFTER_LEXER)
TEST_NAMES = $(BASE_NAMES_BEFORE_LEXER) $(LEXER) $(TEST_NAMES_AFTER_LEXER)
TEST_INTERFACE = $(TEST_NAMES_WITHOUT_LEXER:%=obj/%.cmi) 
TEST_OBJ = $(TEST_NAMES:%=obj/%.cmx) 
#---

IPROVER_BASE_NAME = iprover

#IPROVER_ADD_OBJ_BASE_NAMES = discount instantiation 

ifeq ($(OPT),true)
  COMPILE=$(OCAMLOPT)
  ADDTONAME=opt
  OBJ = $(OBJ_BASE_NAMES:%=obj/%.cmx) 
 # IPROVER_ADD_OBJ = $(IPROVER_ADD_OBJ_BASE_NAMES:%=obj/%.cmx) obj/$(IPROVER_BASE_NAME).cmx
    IPROVER_ADD_OBJ = obj/$(IPROVER_BASE_NAME).cmx
else 	
  IPROVERFLAGS= -custom
  COMPILE=$(OCAMLC)
  OBJ = $(OBJ_BASE_NAMES:%=%.cmo) 
  IPROVER_ADD_OBJ = $(IPROVER_ADD_OBJ_BASE_NAMES:%=%.cmo) 
  CFLAGS    = -I$(OCAMLLIB) -std=c99
endif


ifeq ($(CPP),true)	
  CC = g++
  PROP_SOLVER_NAMES=Solver_cpp minisat_c_wrapper minisat_ocaml_wrapper
  IPROVERFLAGS= -cc g++ -ccopt -L$(OCAMLLIB) -I $(OCAMLLIB)
  CFLAGS = -I$(OCAMLLIB)
  ADDTONAME_CPP="_cpp"	
else
  CC=gcc
  PROP_SOLVER_NAMES= $(CSOLVER) solver_interface 
  CFLAGS = -O3 -I$(OCAMLLIB)
endif

ifeq ($(PROFILE),true)
  OCAMLFLAGS= -p -I obj/ -I util/lib 
  CFLAGS = -I$(OCAMLLIB) -p 
  ADDTONAME=prof
endif


IPROVER_C_OBJ= $(PROP_SOLVER_NAMES:%=obj/%.o)

#INTERFACE = $(BEFORE_PARSING:%=obj/%.cmi) obj/$(PARSER).cmi $(BASE_NAMES:%=obj/%.cmi) 

INTERFACE = $(BASE_NAMES_WITHOUT_LEXER:%=obj/%.cmi) 
#IPROVER_INTERFACE_ADD = $(IPROVER_ADD_OBJ_BASE_NAMES:%=obj/%.cmi)


IPROVER_NAME = $(IPROVER_BASE_NAME)$(ADDTONAME)$(ADDTONAME_CPP)

# $(IPROVER_NAME) : util/lib/minisat.cmxa util/lib/hhlmuc.cmxa \

$(IPROVER_NAME) : util/lib/minisat.cmxa \
		  $(INTERFACE)\
                  $(OBJ) $(IPROVER_C_OBJ) $(IPROVER_ADD_OBJ) src/$(IPROVER_BASE_NAME).ml 
	$(COMPILE) $(IPROVERFLAGS) $(IPROVER_C_OBJ) -o $@ \
        $(OCAMLFLAGS) unix.cmxa str.cmxa util/lib/minisat.cmxa $(OBJ) $(IPROVER_ADD_OBJ)
#        $(OCAMLFLAGS) unix.cmxa str.cmxa util/lib/minisat.cmxa util/lib/hhlmuc.cmxa $(OBJ) $(IPROVER_ADD_OBJ)
#        $(OCAMLFLAGS) unix.cmxa str.cmxa $(OBJ) $(IPROVER_ADD_OBJ) 


# util/lib/minisat.cmxa: export OCAMLLIBDIR=$(OCAMLLIB)
# util/lib/minisat.cmxa: export OCAMLINCDIR=$(OCAMLLIB)

# Better use per-target exports as above, also restore in
# util/lib/hhlmuc.cmxa target below
export OCAMLLIBDIR=$(OCAMLLIB)
export OCAMLINCDIR=$(OCAMLLIB)

util/lib/minisat.cmxa:
	cd util && $(MAKE) -f Makefile minisat-ocaml

# util/lib/hhlmuc.cmxa: export OCAMLLIBDIR=$(OCAMLLIB)
# util/lib/hhlmuc.cmxa: export OCAMLINCDIR=$(OCAMLLIB)

util/lib/hhlmuc.cmxa:
	cd util && $(MAKE) -f Makefile hhlmuc-ocaml

test : $(TEST_INTERFACE)\
       $(TEST_OBJ)
	echo "test passed" > test

#$(IPROVER_NAME) : $(PARSING) $(INTERFACE) $(IPROVER_INTERFACE_ADD)\
#                  $(OBJ) $(IPROVER_C_OBJ) $(IPROVER_ADD_OBJ) src/$(IPROVER_BASE_NAME).ml
#	$(COMPILE) $(IPROVERFLAGS) $(IPROVER_C_OBJ) -o $@ \
#        $(OCAMLFLAGS) unix.cmxa str.cmxa $(OBJ) $(IPROVER_ADD_OBJ) 


#------------satandalone prop solver----------------------------------------

STANDALONE_OBJ=obj/lib.cmx obj/statistics.cmx obj/propSolver.cmx $(IPROVER_C_OBJ)
prop_solver_standalone : $(STANDALONE_OBJ)  src/prop_solver_standalone.ml
	$(COMPILE) $(IPROVERFLAGS)  -o $@ \
        $(OCAMLFLAGS) unix.cmxa str.cmxa $(STANDALONE_OBJ) src/prop_solver_standalone.ml

#----------------------------------------


src/$(LEXER).ml : src/$(LEXER).mll
	ocamllex src/$(LEXER).mll

#generates both mli and ml from mly
src/$(PARSER).mli src/$(PARSER).ml: src/$(PARSER).mly
	ocamlyacc src/$(PARSER).mly



#implicit rules
obj/%.o : src/%.c
	$(CC) $(CFLAGS) -c -o $@ $<

obj/%.o : src/%.C
	$(CC) $(CFLAGS) -c -o $@ $<

obj/%.o : src/%.cpp
	$(CC) $(CFLAGS) -c -o $@ $<


obj/%.cmi : src/%.mli
	$(OCAMLOPT) $(OCAMLFLAGS) -o $@ -c $< 
obj/%.cmx : src/%.ml
	$(OCAMLOPT) $(OCAMLFLAGS) -o $@ -c $<



.PHONY: clean clean-util depend archive

clean: clean-util
	rm -f $(IPROVER_NAME) $(IPROVER_BASE_NAME)prof $(IPROVER_NAME)_cpp src/$(LEXER).ml src/$(PARSER).ml src/$(PARSER).mli obj/*.cmo obj/*.cmx obj/*.cmi obj/*.o

clean-util:
	cd util && $(MAKE) -f Makefile clean


clean_all: clean
	if [ -d $(EPROVER_PATH) ]; then cd $(EPROVER_PATH); make clean; rm -f eprover; cd ../; fi


ARCHIVE_IPROVER_NAMES=./src ./LICENSE ./README ./Makefile ./Makefile.extras ./configure ./Changelog ./problem.p ./problem_sat.p ./problem_fof.p ./util

#use this to temporally adding some names
ARCHIVE_Extras=Makefile_build Makefile_OCamlMakefile OCamlMakefile

#to archive E bundle "make E=true archive"

ifeq ($(E),true) 
   ARCHIVE_NAMES= $(ARCHIVE_IPROVER_NAMES) $(EPROVER_PATH) $(ARCHIVE_Extras)
   ARCHIVE_BASE_DIR="iprover_e_bundle"
else 
   ARCHIVE_NAMES= $(ARCHIVE_IPROVER_NAMES) $(ARCHIVE_Extras)
   ARCHIVE_BASE_DIR="iprover"
endif 

archive:clean_all
	add=$$(date +%Y_%-b_%-d_%-kh); echo $(ARCHIVE_BASE_DIR); new_dir="$(ARCHIVE_BASE_DIR)_$${add}"; name_tar="$${new_dir}.tar.gz"; mkdir $${new_dir}; mkdir "$${new_dir}/obj"; cp -r $(ARCHIVE_NAMES) "$${new_dir}"; pwd; tar -czvf "$${name_tar}" "$${new_dir}"; rm -rf $${new_dir}; if [ -d "Archive" ]; then mv "$${name_tar}" "Archive/"; fi;


#archive_with_e: clean_all
#	add=$$(date +%-d%-b%-kh_%Y); new_dir="iprover_e_bundle_$${add}"; name_tar="$${new_dir}.tar.gz"; mkdir $${new_dir}; mkdir "$${new_dir}/obj"; cp -r $(IPROVER_ARCHIVE_NAMES) ./E_Prover "$${new_dir}"; pwd; tar -czvf "$${name_tar}" "$${new_dir}"; rm -rf $${new_dir}; if [ -d "Archive" ]; then mv "$${name_tar}" "Archive/"; fi;

#make depend to renew dependences
# doesnot work at the moment
#.PHONY: dep
#dep:
#	$(OCAMLDEP) -native $(BASE_NAMES:%=src/%.ml) $(BASE_NAMES:%=src/%.mli) $(IPROVER_ADD_OBJ_BASE_NAMES:%=src/%.ml) $(IPROVER_ADD_OBJ_BASE_NAMES:%=src/%.mli) $(IPROVER_BASE_NAME:%=src/%.ml)  > depend



#include depend
