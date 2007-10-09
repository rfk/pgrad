
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
  * a 'run' is a sequence of Action#Observation pairs, giving the actions
    that were performed and the corresponding observations made by each
    agent.  The most recently performed action is listed first.
  * a 'joint plan' is a prime event structure over Action#Observation
    pairs that specifies the actions to be performed.

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

