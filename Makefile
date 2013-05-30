# first run './configure' to create Makefile.extras
# 'make' for standard version
# make ASSERT=-noassert to switch off asserts which can be more efficient
# 'make CPP=true' for c++ version of minisat
# 'make LGL=true' lingeling for solving/for proofs/unsat cores minisat will still be used
# 'make PicoSAT=true' PicoSAT version

# 'make PROFILE=true' for profile 
# to archive "make archive"
# to archive E bundle "make E=true archive"
# to archive Vampire's clausifier bundle "make V=true archive"
# for debugging "make debug=true", 
#     records backtraces run iproveropt with --dbg_backtrace true

# time iproveropt_lgl --inst_out_proof false --prep_sem_filter none --schedule verification_epr --bmc1_incremental true --bmc1_add_unsat_core none --bmc1_max_bound 10 /M/Intel_Examples/ijcar-paper-cnf/scdpd_miter_full-range.cnf


OCAML=ocaml
OCAMLC=ocamlc
OCAMLOPT=ocamlopt
#OCAMLLIB=/usr/local/lib/ocaml
#OCAMLLIB=/usr/lib/ocaml/3.10.2
#OCAMLLIB is set in Make.extras
EPROVER_PATH="./E_Prover" 
VCLAUSIFIER_PATH="./VClausifier"
OPT=true
OBJPATH=obj/
ADDTONAME=
PROFILE=
C_PROFFLAGS=
OCAMLOPTOPT=ocamlopt.opt
OCAMLDEP=ocamldep
INCLUDES=
# debug=true
debug=
#OCAMLFLAGS=$(INCLUDES)
#OCAMLOPTFLAGS=$(INCLUDES)

#CPP=true for CPP solver
CPP=
OCAMLGRAPH_PATH=./ocamlgraph
#different modifications of MiniSat solver
#CSOLVER=solver_mod_inc_clauses 
CSOLVER=solver
#CSOLVER=solver_basic

ASSERT=
OCAMLFLAGS=-inline 10 $(ASSERT) -annot -I obj/ -I util/lib  -I ocamlgraph/
#OCAMLFLAGS=-I obj/
#LIB  = lib

#LEXER = lexer_tptp lexer_fof
LEXER = lexer_tptp lexer_fof
PARSER = parser_tptp
#BEFORE_PARSING = lib parser_types 
#PARSER_TYPES = parser_types
#PARSING= src/$(LEXER).ml src/$(PARSER).ml

include Makefile.extras


#BASE_NAMES = lib options statistics bit_vec tableArray heap priority_queues tree trie trie_func vectorIndex abstDB abstAssignDB symbol symbolDB var term termDB orderings subst substBound dismatching clause selection clauseAssignDB clauseDB parser_types lexer_tptp parser_tptp parsed_input_to_db parseFiles splitting unif unifIndex discrTree subsetSubsume subsumptionIndex eq_axioms propSolver prop_solver_exchange inference_rules model_inst finite_models preprocess prep_sem_filter large_theories

BASE_NAMES_BEFORE_LEXER = lib hashcons union_find options statistics bit_vec assignMap tableArray heap priority_queues tree trie trie_func vectorIndex abstDB abstAssignDB symbol symbolDB var term termDB orderings subst substBound dismatching clause selection parser_types logic_interface 

#BASE_NAMES_AFTER_LEXER = parser_tptp parsed_input_to_db parseFiles splitting unif unifIndex discrTree subsetSubsume subsumptionIndex eq_axioms propSolver prop_solver_exchange inference_rules model_inst finite_models preprocess prep_sem_filter large_theories discount instantiation

#BASE_NAMES_AFTER_LEXER = parser_tptp parseFiles splitting unif unifIndex discrTree subsetSubsume subsumptionIndex eq_axioms cMinisat propSolver prop_solver_exchange type_inf tstpProof bmc1Axioms inference_rules model_inst finite_models preprocess prep_sem_filter prep_sem_filter_unif large_theories discount instantiation

#large theories are removed at the moment/attaend later
BASE_NAMES_AFTER_LEXER = parser_tptp parseFiles splitting unif unifIndex discrTree subsetSubsume subsumptionIndex eq_axioms cMinisat propSolver prop_solver_exchange type_inf tstpProof bmc1Axioms inference_rules model_inst finite_models prep_sem_filter prep_sem_filter_unif discount instantiation preprocess


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
#OBJ = $(BASE_NAMES_BEFORE_LEXER:%=obj/%.cmx) $(LEXER:%=src/%.ml) $(LEXER:%=obj/%.cmx) $(BASE_NAMES_AFTER_LEXER:%=obj/%.cmx)
 # IPROVER_ADD_OBJ = $(IPROVER_ADD_OBJ_BASE_NAMES:%=obj/%.cmx) obj/$(IPROVER_BASE_NAME).cmx
    IPROVER_ADD_OBJ = obj/$(IPROVER_BASE_NAME).cmx
else 	
  IPROVERFLAGS= -custom
  COMPILE=$(OCAMLC)
  OBJ = $(OBJ_BASE_NAMES:%=%.cmo) 
  IPROVER_ADD_OBJ = $(IPROVER_ADD_OBJ_BASE_NAMES:%=%.cmo) 
  CFLAGS    = -I$(OCAMLLIB) -std=c99
endif

ifeq ($(PROFILE),true)
  OCAMLFLAGS= -p -g -I obj/ -I util/lib -I ocamlgraph
  C_PROFFLAGS = -p -g 
  ADDTONAME=prof

endif


ifeq ($(CPP),true)	
  CC = g++
  PROP_SOLVER_NAMES=Solver_cpp minisat_c_wrapper minisat_ocaml_wrapper
  IPROVERFLAGS= -cc g++ -ccopt -L$(OCAMLLIB) -I $(OCAMLLIB)
  CFLAGS = -I$(OCAMLLIB) $(C_PROFFLAGS)
  ADDTONAME_CPP="_cpp"	
else
ifeq ($(LGL),true)
   CC=gcc
   PROP_SOLVER_NAMES = lglib lgl_ocaml_wrapper
   CFLAGS = -I$(OCAMLLIB) $(C_PROFFLAGS) -Wall -O3 -DNLGLOG -DNDEBUG -DNCHKSOL -DNLGLPICOSAT
  ADDTONAME_CPP="_lgl"	
else
ifeq ($(PicoSAT),true)
   CC=gcc
   PROP_SOLVER_NAMES = picosat picosat_ocaml_wrapper
   CFLAGS = -I$(OCAMLLIB) $(C_PROFFLAGS) -Wall -O3 -DNLGLOG -DNDEBUG -DNCHKSOL -DNLGLPICOSAT
  ADDTONAME_CPP="_picosat"	
else # default C minisat

  CC=gcc
  PROP_SOLVER_NAMES= $(CSOLVER) solver_interface 
  CFLAGS = -O3 -I$(OCAMLLIB) $(C_PROFFLAGS)
endif
endif
endif


ifeq ($(debug),true)
#:= "Simply expanded variable"
#-g for debugging recording backtraces
  OCAMLFLAGS:=$(OCAMLFLAGS) -g
endif

IPROVER_C_OBJ= $(PROP_SOLVER_NAMES:%=obj/%.o)

#INTERFACE = $(BEFORE_PARSING:%=obj/%.cmi) obj/$(PARSER).cmi $(BASE_NAMES:%=obj/%.cmi) 

INTERFACE = $(BASE_NAMES_WITHOUT_LEXER:%=obj/%.cmi) 
#IPROVER_INTERFACE_ADD = $(IPROVER_ADD_OBJ_BASE_NAMES:%=obj/%.cmi)


IPROVER_NAME = $(IPROVER_BASE_NAME)$(ADDTONAME)$(ADDTONAME_CPP)

# $(IPROVER_NAME) : util/lib/minisat.cmxa util/lib/hhlmuc.cmxa \

$(IPROVER_NAME) : util/lib/minisat.cmxa \
		  $(INTERFACE) $(LEXER:%=src/%.ml)\
                  $(OBJ) $(IPROVER_C_OBJ) $(IPROVER_ADD_OBJ) src/$(IPROVER_BASE_NAME).ml 
	$(COMPILE) $(IPROVERFLAGS) $(IPROVER_C_OBJ) -o $@ \
        $(OCAMLFLAGS) unix.cmxa str.cmxa util/lib/minisat.cmxa $(OCAMLGRAPH_PATH)/graph.cmxa $(OBJ) $(IPROVER_ADD_OBJ)
#        $(OCAMLFLAGS) unix.cmxa str.cmxa util/lib/minisat.cmxa util/lib/hhlmuc.cmxa $(OBJ) $(IPROVER_ADD_OBJ)
#        $(OCAMLFLAGS) unix.cmxa str.cmxa $(OBJ) $(IPROVER_ADD_OBJ) 


# util/lib/minisat.cmxa: export OCAMLLIBDIR=$(OCAMLLIB)
# util/lib/minisat.cmxa: export OCAMLINCDIR=$(OCAMLLIB)

# Better use per-target exports as above, also restore in
# util/lib/hhlmuc.cmxa target below
export OCAMLLIBDIR=$(OCAMLLIB)
export OCAMLINCDIR=$(OCAMLLIB)

util/lib/minisat.cmxa:
#	cd util && $(MAKE) -f Makefile minisat-ocaml-profile
	cd util && $(MAKE) -f Makefile minisat-ocaml
#	cd util && $(MAKE) -f Makefile minisat-ocaml-debug

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

STANDALONE_OCAML_NAMES=lib statistics cMinisat options propSolver
STANDALONE_OCAML_INT=$(STANDALONE_OCAML_NAMES:%=obj/%.cmi)
STANDALONE_OCAML_OBJ=$(STANDALONE_OCAML_NAMES:%=obj/%.cmx)
STANDALONE_OBJ=$(STANDALONE_OCAML_OBJ) $(IPROVER_C_OBJ)
prop_solver_standalone :  util/lib/minisat.cmxa $(STANDALONE_OCAML_INT) $(STANDALONE_OBJ)  src/prop_solver_standalone.ml
	$(COMPILE) $(IPROVERFLAGS)  -o $@ \
        $(OCAMLFLAGS) unix.cmxa str.cmxa  util/lib/minisat.cmxa $(STANDALONE_OBJ) src/prop_solver_standalone.ml

#----------------------------------------


#src/$(LEXER).ml : $(@l)
#$(LEXER:%=src/%.ml) : $(@l)
#	ocamllex $<

#$(LEXER:%=src/%.ml) : $(LEXER:%=src/%.mll) 
#	ocamllex $<

src/lexer_tptp.ml : src/lexer_tptp.mll
	ocamllex $<

src/lexer_fof.ml : src/lexer_fof.mll
	ocamllex $<


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



.PHONY : clean clean-util depend archive docs

docs: $(INTERFACE)
	ocamldoc -dot -I obj/ -I util/lib -d docs $(BASE_NAMES_WITHOUT_LEXER:%=src/%.mli) $(BASE_NAMES_WITHOUT_LEXER:%=src/%.ml) src/$(IPROVER_BASE_NAME).ml

clean: clean-util
	rm -f $(IPROVER_NAME) $(IPROVER_NAME)_picosat $(IPROVER_NAME)_lgl $(IPROVER_NAME)_cpp $(IPROVER_BASE_NAME)prof $(IPROVER_NAME)_cpp $(LEXER:%=src/%.ml) src/$(PARSER).ml src/$(PARSER).mli obj/*.cmo obj/*.cmx obj/*.cmi obj/*.o

clean-util:
	cd util && $(MAKE) -f Makefile clean

clean_all: clean
	if [ -d $(EPROVER_PATH) ]; then cd $(EPROVER_PATH); make clean; rm -f eprover; cd ../; fi;\
	if [ -d $(VCLAUSIFIER_PATH) ]; then cd $(VCLAUSIFIER_PATH); make clean; rm -f vclausify_rel; cd ../; fi;\
    if [ -d $(OCAMLGRAPH_PATH) ]; then cd $(OCAMLGRAPH_PATH); make clean; cd ../; fi

ARCHIVE_IPROVER_NAMES=./src ./LICENSE ./LICENSE_PicoSAT ./COPYING_Lingeling ./LICENSE_MiniSAT ./LICENSE_OCAMLGRAPH ./README ./Makefile ./Makefile.extras ./configure ./iproveropt_run.sh ./iproveropt_run_sat.sh ./Changelog ./problem.p ./problem_sat.p ./problem_fof.p ./util ./README.iProver_LTB ./LTB.batch ./README.CASC-J6 ./README.CADE-24

ARCHIVE_LTB_NAMES=./LTB/iprover_sine.sh ./LTB/iprover_sine_single.sh ./LTB/iprover_sine_turing.sh ./LTB/iprover_sine_reduced_cores.sh ./LTB/create_ltb_batch.sh ./LTB/Makefile ./LTB/TreeLimitedRun.c ./LTB/MZR.header ./LTB/MZR_turing.header ./LTB/SMO.header ./LTB/ISA.header ./LTB/MZR_bushy_rand_100.list ./LTB/MZR_chainy_rand_100.list ./LTB/SMO_2011.list ./LTB/ISA_2011.list ./LTB/MZR_bushy.list ./LTB/MZR_chainy.list

#ARCHIVE_LTB_NAMES=./LTB

#use this to temporally adding some names
ARCHIVE_Extras=Makefile_build Makefile_OCamlMakefile OCamlMakefile $(OCAMLGRAPH_PATH)


#to archive E bundle "make E=true archive"

ifeq ($(E),true) 
   ARCHIVE_NAMES= $(ARCHIVE_IPROVER_NAMES) $(EPROVER_PATH) $(ARCHIVE_Extras)
   ARCHIVE_BASE_DIR="iprover_e_bundle"
else 
 ifeq ($(V),true)
  ARCHIVE_NAMES= $(ARCHIVE_IPROVER_NAMES) $(VCLAUSIFIER_PATH) $(ARCHIVE_Extras) $
  ARCHIVE_BASE_DIR="iprover_vampire_clausifier_bundle"
 else	
   ARCHIVE_NAMES= $(ARCHIVE_IPROVER_NAMES) $(ARCHIVE_Extras)
   ARCHIVE_BASE_DIR="iprover"
 endif
endif 

archive:clean_all
	add=$$(date +%Y_%-b_%-d_%-kh); echo $(ARCHIVE_BASE_DIR); new_dir="$(ARCHIVE_BASE_DIR)_$${add}"; name_tar="$${new_dir}.tar.gz"; mkdir $${new_dir}; mkdir "$${new_dir}/obj"; mkdir "$${new_dir}/LTB"; cp -r $(ARCHIVE_NAMES) "$${new_dir}"; cp -r $(ARCHIVE_LTB_NAMES) "$${new_dir}/LTB/"; pwd; tar -czvf "$${name_tar}" "$${new_dir}"; rm -rf $${new_dir}; if [ -d "Archive" ]; then mv "$${name_tar}" "Archive/"; fi;


#archive_with_e: clean_all
#	add=$$(date +%-d%-b%-kh_%Y); new_dir="iprover_e_bundle_$${add}"; name_tar="$${new_dir}.tar.gz"; mkdir $${new_dir}; mkdir "$${new_dir}/obj"; cp -r $(IPROVER_ARCHIVE_NAMES) ./E_Prover "$${new_dir}"; pwd; tar -czvf "$${name_tar}" "$${new_dir}"; rm -rf $${new_dir}; if [ -d "Archive" ]; then mv "$${name_tar}" "Archive/"; fi;

#make depend to renew dependences
# doesnot work at the moment
#.PHONY: dep
#dep:
#	$(OCAMLDEP) -native $(BASE_NAMES:%=src/%.ml) $(BASE_NAMES:%=src/%.mli) $(IPROVER_ADD_OBJ_BASE_NAMES:%=src/%.ml) $(IPROVER_ADD_OBJ_BASE_NAMES:%=src/%.mli) $(IPROVER_BASE_NAME:%=src/%.ml)  > depend

#.PHONY: depend

#depend:
#	ocamldep -native src/*.mli src/*.ml src/*.h src/*.cpp src/*.hpp src/*.c > depend

#include depend
