HHLMUC - Haifa's High Level Minimal Unsatisfiable Core solver.
==============================================================
Based on Minisat 2.2 (http://minisat.se/downloads/minisat-2.2.0.tar.gz)

Written by Vadim Ryvchin.



Description:
------------
A description of hhlmuc appears in:

Faster Extraction of High-Level Minimal Unsatisfiable Cores / Vadim
Ryvchin, Ofer Strichman. To appear in SAT'11



Executable:
-----------

The file hhlmuc is a statically built version of the solver on
Linux (64-bit).



Build from source files:
------------------------

1. Make sure that zlib is installed on your machine (http://zlib.net/)

2. Update the directory location in the file build.sh

3. Make sure build.sh is executable (if not then 'chmod +x build.sh' will fix this)

4. run build.sh



Usage:
------
To run the solver simply type:

hhlmuc <benchmark file> [additional flags]

The format of the file is gcnf. This is an extension of the standard Dimacs cnf format.
It means that each clause is preceded by {0} if it is a remainder clause or {<id>} if it is part
of constraint # <id>. For example:

p gcnf 3 7 4
{0} 1 2 3 0
{1} -1 2 0
{1} -2 3 0
{2} -3 0
{3} 2 -3 0
{3} -2 -3 0
{4} -2 3 0


The output of hhlmuc includes a line starting with 'v', that lists
the constraints that participate in the proof. In the example above
it will be: v 1 2 0, meaning that constraints 1 and 2 are
sufficient for a proof.



Flags:
------
Type hhlmuc --help for a list of options.

The names of the flags below are mapped to options B -- G in the above
article. Each option can be preceded with 'no-' to deactivate.

B. -no-ic-simplify (don't perform minimization over IC clauses) -- default

C. -post-ic-imp (postpone implications on IC clauses)-- default

D. -bind-as-orig=<#> (where <#> is one of:
    0 - add IC clauses as is (marked as IC clauses),
    1 - add IC clauses as remainder clauses
    2 - add IC clauses + inferred cone as remainder clauses -- default.
    )

E. -ic-as-dec (treat IC implications as decisions) -- default

   -dec-<literal> (where 'literal' is one of 'l1' or 'l2', corresponding to Fig 1. in the article.
                   This option should only be activated together with -ic-as-dec. Default is 'l1')

F. -no-full-bck - (don't perform backtrack in case of conflict from ic-as-dec)


G. -remove_order=<#> (where # is one of:
    0 - largest participation in unsat core -- default,
    1 - lowest participation in unsat core,
    2 - biggest constraint index,
    3 - lowest constraint index.
    )


In addition you may want to play with:

-no-pre (no preprocessing)

-no-glucose (do not activate 'glucose-style' clause deletion strategy, i.e., delete clauses not based on the conflict participation, but rather
             only based on the # of different decision levels in the learned clause)

-no-local-restart (do not activate local restarts -- see 'Local Restarts' in SAT'09 by the same authors) -- default



Usage examples:
---------------
1. The default (no parameters) is what was sent to the competition:

hhlmuc test/ex.gcnf


It is equivalent to:

hhlmuc test/ex.gcnf -pre -no-ic-simplify -post-ic-imp -ic-as-dec -bind-as-orig=2 -full-bck -dec-l1 -remove-order=0 -glucose -no-local-restart


2. The configuration corresponding to options A-G in the article can be obtained by:

hhlmuc test/ex.gcnf -no-pre -no-ic-simplify -bind-as-orig=2 -post-ic-imp -ic-as-dec -no-full-bck -dec-l1 -remove-order=2 -no-glucose -no-local-restart




Further information:
--------------------

Questions should be referred to: vadimryv@gmail.com
