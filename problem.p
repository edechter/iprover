%--------------------------------------------------------------------------
% File     : PUZ039-1 : TPTP v3.7.0. Bugfixed v2.6.0.
% Domain   : Puzzles
% Problem  : Quo vadis 2
% Version  : Especial.
% English  : bb is big block (square, size=4 tiles).
%            s1-s4 : 4 small square blocks, size=1 tile
%            v1-v4: 4 vertical blocks, size= 2 tiles
%            b1: horizontal block, size= 2 tiles
%            e1, e2 are the 2 blank tiles
%            It's a 5x4 playing field to move from the start state to
%            the goal state. This is an intermediate goal for testing.

% Refs     : 
% Source   : [TPTP]
% Names    : 

% Status   : Unsatisfiable
% Rating   : 0.14 v3.4.0, 0.00 v3.2.0, 0.67 v3.1.0, 0.33 v2.7.0, 0.25 v2.6.0
% Syntax   : Number of clauses     :   43 (   0 non-Horn;   2 unit;  43 RR)
%            Number of atoms       :   84 (   0 equality)
%            Maximal clause size   :    2 (   2 average)
%            Number of predicates  :    1 (   0 propositional; 12-12 arity)
%            Number of functors    :   14 (   1 constant; 0-2 arity)
%            Number of variables   :  491 (  11 singleton)
%            Maximal term depth    :    6 (   1 average)

% Comments : 
% Bugfixes : v2.6.0 - Fixed clause goal_state.
%--------------------------------------------------------------------------

cnf(s1_right,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,s1(X,Y),S2,S3,S4,e1(X,s(Y)),E2)
    | state(B,V1,V2,V3,V4,H,s1(X,s(Y)),S2,S3,S4,e1(X,Y),E2) )).

cnf(s1_left,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,s1(X,s(Y)),S2,S3,S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,s1(X,Y),S2,S3,S4,e1(X,s(Y)),E2) )).

cnf(s1_down,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,s1(X,Y),S2,S3,S4,e1(s(X),Y),E2)
    | state(B,V1,V2,V3,V4,H,s1(s(X),Y),S2,S3,S4,e1(X,Y),E2) )).

cnf(s1_up,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,s1(s(X),Y),S2,S3,S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,s1(X,Y),S2,S3,S4,e1(s(X),Y),E2) )).

cnf(s2_right,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,s2(X,Y),S3,S4,e1(X,s(Y)),E2)
    | state(B,V1,V2,V3,V4,H,S1,s2(X,s(Y)),S3,S4,e1(X,Y),E2) )).

cnf(s2_left,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,s2(X,s(Y)),S3,S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,s2(X,Y),S3,S4,e1(X,s(Y)),E2) )).

cnf(s2_down,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,s2(X,Y),S3,S4,e1(s(X),Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,s2(s(X),Y),S3,S4,e1(X,Y),E2) )).

cnf(s2_up,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,s2(s(X),Y),S3,S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,s2(X,Y),S3,S4,e1(s(X),Y),E2) )).

cnf(s3_right,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,s3(X,Y),S4,e1(X,s(Y)),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,s3(X,s(Y)),S4,e1(X,Y),E2) )).

cnf(s3_left,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,s3(X,s(Y)),S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,s3(X,Y),S4,e1(X,s(Y)),E2) )).

cnf(s3_down,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,s3(X,Y),S4,e1(s(X),Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,s3(s(X),Y),S4,e1(X,Y),E2) )).

cnf(s3_up,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,s3(s(X),Y),S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,s3(X,Y),S4,e1(s(X),Y),E2) )).

cnf(s4_right,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(X,Y),e1(X,s(Y)),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(X,s(Y)),e1(X,Y),E2) )).

cnf(s4_left,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(X,s(Y)),e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(X,Y),e1(X,s(Y)),E2) )).

cnf(s4_down,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(X,Y),e1(s(X),Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(s(X),Y),e1(X,Y),E2) )).

cnf(s4_up,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(s(X),Y),e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,H,S1,S2,S3,s4(X,Y),e1(s(X),Y),E2) )).

cnf(v1_right,axiom,
    ( ~ state(B,v1(X,Y),V2,V3,V4,H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y)))
    | state(B,v1(X,s(Y)),V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y)) )).

cnf(v1_left,axiom,
    ( ~ state(B,v1(X,s(Y)),V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y))
    | state(B,v1(X,Y),V2,V3,V4,H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y))) )).

cnf(v1_down,axiom,
    ( ~ state(B,v1(X,Y),V2,V3,V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),E2)
    | state(B,v1(s(X),Y),V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),E2) )).

cnf(v1_up,axiom,
    ( ~ state(B,v1(s(X),Y),V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),E2)
    | state(B,v1(X,Y),V2,V3,V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),E2) )).

cnf(v2_right,axiom,
    ( ~ state(B,V1,v2(X,Y),V3,V4,H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y)))
    | state(B,V1,v2(X,s(Y)),V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y)) )).

cnf(v2_left,axiom,
    ( ~ state(B,V1,v2(X,s(Y)),V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y))
    | state(B,V1,v2(X,Y),V3,V4,H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y))) )).

cnf(v2_down,axiom,
    ( ~ state(B,V1,v2(X,Y),V3,V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),E2)
    | state(B,V1,v2(s(X),Y),V3,V4,H,S1,S2,S3,S4,e1(X,Y),E2) )).

cnf(v2_up,axiom,
    ( ~ state(B,V1,v2(s(X),Y),V3,V4,H,S1,S2,S3,S4,e1(X,Y),E2)
    | state(B,V1,v2(X,Y),V3,V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),E2) )).

cnf(v3_right,axiom,
    ( ~ state(B,V1,V2,v3(X,Y),V4,H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y)))
    | state(B,V1,V2,v3(X,s(Y)),V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y)) )).

cnf(v3_left,axiom,
    ( ~ state(B,V1,V2,v3(X,s(Y)),V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y))
    | state(B,V1,V2,v3(X,Y),V4,H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y))) )).

cnf(v3_down,axiom,
    ( ~ state(B,V1,V2,v3(X,Y),V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),E2)
    | state(B,V1,V2,v3(s(X),Y),V4,H,S1,S2,S3,S4,e1(X,Y),E2) )).

cnf(v3_up,axiom,
    ( ~ state(B,V1,V2,v3(s(X),Y),V4,H,S1,S2,S3,S4,e1(X,Y),E2)
    | state(B,V1,V2,v3(X,Y),V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),E2) )).

cnf(v4_right,axiom,
    ( ~ state(B,V1,V2,V3,v4(X,Y),H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y)))
    | state(B,V1,V2,V3,v4(X,s(Y)),H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y)) )).

cnf(v4_left,axiom,
    ( ~ state(B,V1,V2,V3,v4(X,s(Y)),H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y))
    | state(B,V1,V2,V3,v4(X,Y),H,S1,S2,S3,S4,e1(X,s(Y)),e2(s(X),s(Y))) )).

cnf(v4_down,axiom,
    ( ~ state(B,V1,V2,V3,v4(X,Y),H,S1,S2,S3,S4,e1(s(s(X)),Y),E2)
    | state(B,V1,V2,V3,v4(s(X),Y),H,S1,S2,S3,S4,e1(X,Y),E2) )).

cnf(v4_up,axiom,
    ( ~ state(B,V1,V2,V3,v4(s(X),Y),H,S1,S2,S3,S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,v4(X,Y),H,S1,S2,S3,S4,e1(s(s(X)),Y),E2) )).

cnf(h_right,axiom,
    ( ~ state(B,V1,V2,V3,V4,h(X,Y),S1,S2,S3,S4,e1(X,s(s(Y))),E2)
    | state(B,V1,V2,V3,V4,h(X,s(Y)),S1,S2,S3,S4,e1(X,Y),E2) )).

cnf(h_left,axiom,
    ( ~ state(B,V1,V2,V3,V4,h(X,s(Y)),S1,S2,S3,S4,e1(X,Y),E2)
    | state(B,V1,V2,V3,V4,h(X,Y),S1,S2,S3,S4,e1(X,s(s(Y))),E2) )).

cnf(h_down,axiom,
    ( ~ state(B,V1,V2,V3,V4,h(X,Y),S1,S2,S3,S4,e1(s(X),Y),e2(s(X),s(Y)))
    | state(B,V1,V2,V3,V4,h(s(X),Y),S1,S2,S3,S4,e1(X,Y),e2(X,s(Y))) )).

cnf(h_up,axiom,
    ( ~ state(B,V1,V2,V3,V4,h(s(X),Y),S1,S2,S3,S4,e1(X,Y),e2(X,s(Y)))
    | state(B,V1,V2,V3,V4,h(X,Y),S1,S2,S3,S4,e1(s(X),Y),e2(s(X),s(Y))) )).

cnf(b_right,axiom,
    ( ~ state(bb(X,Y),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(X,s(s(Y))),e2(s(X),s(s(Y))))
    | state(bb(X,s(Y)),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y)) )).

cnf(b_left,axiom,
    ( ~ state(bb(X,s(Y)),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(s(X),Y))
    | state(bb(X,Y),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(X,s(s(Y))),e2(s(X),s(s(Y)))) )).

cnf(b_down,axiom,
    ( ~ state(bb(X,Y),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),e2(s(s(X)),s(Y)))
    | state(bb(s(X),Y),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(X,s(Y))) )).

cnf(b_up,axiom,
    ( ~ state(bb(s(X),Y),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(X,s(Y)))
    | state(bb(X,Y),V1,V2,V3,V4,H,S1,S2,S3,S4,e1(s(s(X)),Y),e2(s(s(X)),s(Y))) )).

cnf(swap_blanks,axiom,
    ( ~ state(B,V1,V2,V3,V4,H,S1,S2,S3,S4,e1(X,Y),e2(Q,W))
    | state(B,V1,V2,V3,V4,H,S1,S2,S3,S4,e1(Q,W),e2(X,Y)) )).

%------------------------------------------------------------------------------


cnf(initial_state,hypothesis,
    ( state(bb(o,s(o)),v1(o,o),v2(o,s(s(s(o)))),v3(s(s(o)),o),v4(s(s(o)),s(s(s(o)))),h(s(s(o)),s(o)),s1(s(s(s(o))),s(o)),s2(s(s(s(o))),s(s(o))),s3(s(s(s(s(o)))),s(o)),s4(s(s(s(s(o)))),s(s(o))),e1(s(s(s(s(o)))),o),e2(s(s(s(s(o)))),s(s(s(o))))) )).

cnf(goal_state,negated_conjecture,
    ( ~ state(B,V1,V2,V3,v4(s(s(o)),s(s(o))),H,S1,S2,S3,S4,E1,E2) )).
