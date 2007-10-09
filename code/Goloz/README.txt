
Goloz: Implementation of MIndiGolog using Oz

This is a full implementation of the multi-agent Golog variant "MIndiGolog"
using Oz/Mozart as a distributed logic programming platform.  It allows
a team of agents to cooperatively plan and perform an execution of a shared
MIndiGolog program.

Import concepts:

  * a 'step' is a single transition of a program, and it holds all the
    necesary metadata about what was performed and why.  In particular:
        - the action that was performed (or nil if no action)
        - any explicit preconditions that held before the step
        - the thread of execution to which it belongs
        - the observations made by each agent as a result of the step
  * a 'run' is a sequence of steps that have been performed, most recent
    step first.  It is thus simlar to a situation but also includes the
    observations made by each agent.
  * a 'joint plan' is a prime event structure over steps that specifies
    the actions to be performed, depending on the observations made.

Record labels used to build program terms:

   nil
   test
   seq
   either
   pick
   star
   ifte
   wloop
   conc
   pconc
   cstar
   pcall

