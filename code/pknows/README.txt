
Reasoning Engine for Complex Epistemic Modalities in the Situation Calculus

This is a simplistic prolog implementation of epistemic reasoning in the
situation calculus, using techniques from the paper "Common Knowledge,
Hidden Actions, and the Frame Problem".

Concurrent actions are not currently supported, although this is purely
an implementation limit.

Fluents are reified for easy manipulation, with the predicate "holds"
evaluating a fluent at a given situation.  Used like so:

    ?- [main].
    true.

    ?- holds(loc(c),s0).
    true.

    ?- holds(knows(ann,loc(C)),s0).
    fail.

    ?- holds(knows(ann,loc(C)),do(read(ann),s0)).
    true.


We assume all variables have a finite domain, so that fluents can be
propositionalized to perform reasoning.  We shell out of the PDL prover
from the Tableuax Workbench project for the actual reasoning.

The included files are:

  * fluent.pl:  Create and manipulate reified fluent terms.  This file also
                provides simplication routines to help keep the size of
                fluent terms manageable.

  * epath.pl:   Create and manipulate epistemic path terms.  This is pretty
                similar in scope to fluent.pl.

  * twb_pdl.pl:  Interface with the PDL prover for the Tableaux Workbench
                 project to static epistemic reasoning.

  * sitcalc.pl:  Domain-independent sitcalc primitives, such as regression()
                 and holds().

  * domain.pl:  Domain-specific predicates, such as ADP fluent definitions,
                causes_true/causes_false, etc.


