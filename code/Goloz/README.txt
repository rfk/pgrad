
Goloz: Implementation of MIndiGolog using Oz

This is a full implementation of the multi-agent Golog variant "MIndiGolog"
using Oz/Mozart as a distributed logic programming platform.  It consists
of the following files:

  LP.oz:    Basic logic-programming predicates (to make things a little
            more like prolog).

  FOF.oz:   Implements first-order formulae as an abstract data type,
            including inferencing precedures.

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

