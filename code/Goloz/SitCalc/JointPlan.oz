%
%  JointPlan.oz
%
%  Implements a joint plan of execution, a prime event structure over the
%  (action-bearing) steps of execution of the program that can be performed
%  in a reactive manner by the agents.
%
%  Each event in the execution is uniquely identified by an integer,
%  which is its order of insertion into the plan.
%


functor

import

  LP at '../Utils/LP.ozf'
  MList at '../Utils/MList.ozf'
  SitCalc

export

  Init
  Insert
  Assert
  Finish

  Enablers
  Alternatives
  Preceeds
  Conflicting
  Distinguishable

  NextEvents
  GetEvent

define

  %
  %  Initialize a new (empty) joint plan.
  %
  proc {Init JP}
    JP = jp(count: 0
            enablers: e()
            alternatives: a() 
            distinguishable: d()
           )
  end

  %
  %  List the events that enable the given event N.
  %
  proc {Enablers JP N Ns}
    Ns = JP.enablers.N
  end

  %
  %  List the events that could occur instead of the given event N.
  %
  proc {Alternatives JP N Ns}
    Ns = JP.alternatives.N
  end

  %
  %  Determine whether event N1 is required to happen before event N2.
  %
  proc {Preceeds JP N1 N2 B}
    if {List.member N1 JP.enablers.N2} then
      B = true
    else
      B = for return:R default:false Ne in JP.enablers.N2 do
            if {Preceeds JP N1 Ne} then {R true} end
          end
    end
  end

  %
  %  Determine whether events N1 and N2 are in conflict, i.e. they
  %  cannot appear together in a run.
  %
  proc {Conflicting JP N1 N2 B}
    if {List.member N2 JP.alternatives.N1} then
      B = true
    else
      B = for return:R default:false Na in JP.alternatives.N1 do
            if {Preceeds JP Na N2} then {R true} end
          end
    end
  end

  %
  %  Determine whether events N1 and N2 are distinguishable from
  %  the perspective of agent A.  This is true if and only if
  %  every run up to N1 produces a different observation history
  %  for A than every run up to N2.
  %
  proc {Distinguishable JP A N1 N2 B}
    B = JP.distinguishable.N1.N2.A
  end

  %
  %  Insert a new step into the joint plan.  Returns a list
  %  of event IDs representing the possible outcomes of performing
  %  that step.  These events are {Alternatives} to each other.
  %  {Preceeds} is a function that will be called with an existing
  %  step as its only argument.  It must return true if that step
  %  is required to preceed the new step, false otherwise.
  %
  proc {Insert JPIn Step Preceeds JPOut Outcomes}
    JPIn = JPOut
    Outcomes = nil
  end

end
