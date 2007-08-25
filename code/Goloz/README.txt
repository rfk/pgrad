
Goloz: Implementation of MIndiGolog using Oz

This is a full implementation of the multi-agent Golog variant "MIndiGolog"
using Oz/Mozart as a distributed logic programming platform.  It consists
of the following files:

  OpenMap.oz:  A key->value mapping class using open-ended lists, meaning it
               can be constructed a piece at a time.

  ListDict.oz: Dictionary class clone that accepts lists of records as its
               keys, rather than simple atoms.

  LP.oz:    Basic logic-programming predicates (to make things a little
            more like prolog).

  BDD.oz:   A generic library for handling and exploring BDD-like structures.
            Includes memoization.

  FOF.oz:   Implements almost-first-order formulae that are suitable to our
            needs, including a complete inference procedure.  This is *not*
            a full first-order theorem prover, but close enough.

  Time.oz:  Implements time-points as an abstract data type.  At the moment,
            they're simply integers.

  Sitcalc.oz:  Domain-independent procedures for doing reasoning in the
               situation calculus, e.g. regression.

  MIndiGolog.oz:  Transition semantics of MIndiGolog, defined over 'executions'
                  rather than vanilla situation terms.

  Domain.oz:   Defines the behavior of the particular domain being modelled.
               Things like possibility and successor-state axioms go here.

  Program.oz:  Defnition of the control program, including procedure
               definitions.

  Agent.oz:    Specifics of the agent represented by this particular Oz
               instance.  Each agent in the team will thus have a different
               version of this file.

  Goloz.oz:    Root functor, top-level program entry point.

