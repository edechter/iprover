%--------------------------------------------------------------------------
% File     : GRP132-2.005 : TPTP v3.7.0. Released v1.2.0.
% Domain   : Group Theory (Quasigroups)
% Problem  : (3,1,2) conjugate orthogonality, no idempotence
% Version  : [Sla93] axioms : Augmented. 
% English  : Generate the multiplication table for the specified quasi-
%            group with 5 elements.

% Refs     : [FSB93] Fujita et al. (1993), Automatic Generation of Some Res
%          : [Sla93] Slaney (1993), Email to G. Sutcliffe
%          : [SFS95] Slaney et al. (1995), Automated Reasoning and Exhausti
% Source   : [TPTP]
% Names    : 

% Status   : Satisfiable
% Rating   : 0.00 v3.4.0, 0.40 v3.3.0, 0.00 v3.2.0, 0.50 v2.6.0, 0.67 v2.5.0, 0.60 v2.4.0, 0.67 v2.2.0, 1.00 v2.1.0
% Syntax   : Number of clauses     :   46 (   1 non-Horn;  39 unit;  46 RR)
%            Number of atoms       :   68 (   0 equality)
%            Maximal clause size   :    7 (   1 average)
%            Number of predicates  :    5 (   0 propositional; 1-3 arity)
%            Number of functors    :    5 (   5 constant; 0-0 arity)
%            Number of variables   :   29 (   0 singleton)
%            Maximal term depth    :    1 (   1 average)

% Comments : Slaney's [1993] axiomatization has been modified for this.
%          : Substitution axioms are not needed, as any positive equality
%            literals should resolve on negative ones directly.
%          : As in GRP130-1, either one of qg2_1 or qg2_2 may be used, as 
%            each implies the other in this scenario, with the help of 
%            cancellation. The dependence cannot be proved, so both have 
%            been left in here.
%          : This version adds a simple isomorphism avoidance clause,
%            mentioned in [FSB93].
%          : tptp2X: -f tptp -s5 GRP132-2.g 
%--------------------------------------------------------------------------
cnf(e_1_then_e_2,axiom,
    ( next(e_1,e_2) )).

cnf(e_2_then_e_3,axiom,
    ( next(e_2,e_3) )).

cnf(e_3_then_e_4,axiom,
    ( next(e_3,e_4) )).

cnf(e_4_then_e_5,axiom,
    ( next(e_4,e_5) )).

cnf(e_2_greater_e_1,axiom,
    ( greater(e_2,e_1) )).

cnf(e_3_greater_e_1,axiom,
    ( greater(e_3,e_1) )).

cnf(e_4_greater_e_1,axiom,
    ( greater(e_4,e_1) )).

cnf(e_5_greater_e_1,axiom,
    ( greater(e_5,e_1) )).

cnf(e_3_greater_e_2,axiom,
    ( greater(e_3,e_2) )).

cnf(e_4_greater_e_2,axiom,
    ( greater(e_4,e_2) )).

cnf(e_5_greater_e_2,axiom,
    ( greater(e_5,e_2) )).

cnf(e_4_greater_e_3,axiom,
    ( greater(e_4,e_3) )).

cnf(e_5_greater_e_3,axiom,
    ( greater(e_5,e_3) )).

cnf(e_5_greater_e_4,axiom,
    ( greater(e_5,e_4) )).

cnf(no_redundancy,axiom,
    ( ~ product(X,e_1,Y)
    | ~ next(X,X1)
    | ~ greater(Y,X1) )).

cnf(element_1,axiom,
    ( group_element(e_1) )).

cnf(element_2,axiom,
    ( group_element(e_2) )).

cnf(element_3,axiom,
    ( group_element(e_3) )).

cnf(element_4,axiom,
    ( group_element(e_4) )).

cnf(element_5,axiom,
    ( group_element(e_5) )).

cnf(e_1_is_not_e_2,axiom,
    ( ~ equalish(e_1,e_2) )).

cnf(e_1_is_not_e_3,axiom,
    ( ~ equalish(e_1,e_3) )).

cnf(e_1_is_not_e_4,axiom,
    ( ~ equalish(e_1,e_4) )).

cnf(e_1_is_not_e_5,axiom,
    ( ~ equalish(e_1,e_5) )).

cnf(e_2_is_not_e_1,axiom,
    ( ~ equalish(e_2,e_1) )).

cnf(e_2_is_not_e_3,axiom,
    ( ~ equalish(e_2,e_3) )).

cnf(e_2_is_not_e_4,axiom,
    ( ~ equalish(e_2,e_4) )).

cnf(e_2_is_not_e_5,axiom,
    ( ~ equalish(e_2,e_5) )).

cnf(e_3_is_not_e_1,axiom,
    ( ~ equalish(e_3,e_1) )).

cnf(e_3_is_not_e_2,axiom,
    ( ~ equalish(e_3,e_2) )).

cnf(e_3_is_not_e_4,axiom,
    ( ~ equalish(e_3,e_4) )).

cnf(e_3_is_not_e_5,axiom,
    ( ~ equalish(e_3,e_5) )).

cnf(e_4_is_not_e_1,axiom,
    ( ~ equalish(e_4,e_1) )).

cnf(e_4_is_not_e_2,axiom,
    ( ~ equalish(e_4,e_2) )).

cnf(e_4_is_not_e_3,axiom,
    ( ~ equalish(e_4,e_3) )).

cnf(e_4_is_not_e_5,axiom,
    ( ~ equalish(e_4,e_5) )).

cnf(e_5_is_not_e_1,axiom,
    ( ~ equalish(e_5,e_1) )).

cnf(e_5_is_not_e_2,axiom,
    ( ~ equalish(e_5,e_2) )).

cnf(e_5_is_not_e_3,axiom,
    ( ~ equalish(e_5,e_3) )).

cnf(e_5_is_not_e_4,axiom,
    ( ~ equalish(e_5,e_4) )).

cnf(product_total_function1,axiom,
    ( ~ group_element(X)
    | ~ group_element(Y)
    | product(X,Y,e_1)
    | product(X,Y,e_2)
    | product(X,Y,e_3)
    | product(X,Y,e_4)
    | product(X,Y,e_5) )).

cnf(product_total_function2,axiom,
    ( ~ product(X,Y,W)
    | ~ product(X,Y,Z)
    | equalish(W,Z) )).

cnf(product_right_cancellation,axiom,
    ( ~ product(X,W,Y)
    | ~ product(X,Z,Y)
    | equalish(W,Z) )).

cnf(product_left_cancellation,axiom,
    ( ~ product(W,Y,X)
    | ~ product(Z,Y,X)
    | equalish(W,Z) )).

cnf(qg2_1,negated_conjecture,
    ( ~ product(X1,Y1,Z1)
    | ~ product(X2,Y2,Z1)
    | ~ product(Z2,X1,Y1)
    | ~ product(Z2,X2,Y2)
    | equalish(X1,X2) )).

cnf(qg2_2,negated_conjecture,
    ( ~ product(X1,Y1,Z1)
    | ~ product(X2,Y2,Z1)
    | ~ product(Z2,X1,Y1)
    | ~ product(Z2,X2,Y2)
    | equalish(Y1,Y2) )).

%--------------------------------------------------------------------------
