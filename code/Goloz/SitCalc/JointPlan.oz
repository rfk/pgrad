%
%  JointPlan.oz
%
%  Implements a joint plan of execution, a prime event structure over the
%  (action-bearing) steps of execution of the program that can be performed
%  in a reactive manner by the agents.
%
%  Each event in the execution is uniquely identified by an integer,
%  which is its order of insertion into the plan.  A run is identified
%  by a sorted list of integers, with largest integer first.  It is the
%  unique run containing all events in the list.  These lists are what
%  is reported to the outside world in various event query functions.
%


functor

import

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

define

  %
  %  Initialize a new (empty) joint plan.
  %
  proc {Init JP}
    JP = jp(count: 0
            events: unit(0: start)
            enablers: unit()
            alternatives: unit() 
            distinguishable: unit()
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
  %  Insert a new set of steps into the joint plan.  Returns a list
  %  of event IDs representing each step, in order. The steps will be
  %  added as mutually exclusive alternatives to each other.
  %  {Preceeds} is a function that will be called with an existing
  %  step seqn as its only argument.  It must return true if that step
  %  is required to preceed the new steps, false otherwise.
  %
  proc {Insert JPIn NewSs Preceeds JPOut Outcomes}
    Ens NewNs JP2 JP3
  in
    {FindEnablers JPIn JPIn.count Preceeds nil Ens}
    {AddNewEvents JPIn NewSs Ens JP2 NewNs}
    {SetAsAlternatives JP2 NewNs nil JP3}
    {AddIndistinguishableEvents JP3 NewNs JPOut}
  end

  proc {FindEnablers JP N PFunc ESoFar Ens}
    if N < 0 then Ens = SoFar
    else Conflicts in
      Conflicts = for return:R default:true E in ESoFar do
                    if {Conflicting JP N E} then {R false} end
                  end
      if {Neg Conflicts} then Preceeds in
        Preceeds = for return:R default:false E in ESoFar do
                      if {Preceeds JP N E} then {R true} end
                   end
        if Preceeds then
          {FindEnablers JP N-1 PFunc ESoFar Ens}
        else
          if {PFunc N} then
            {FindEnablers JP N-1 PFunc N|ESoFar Ens}
          else
            {FindEnablers JP N-1 PFunc ESoFar Ens}
          end
        end
      else
        {FindEnablers JP N-1 PFunc ESoFar Ens}
      end
    end
  end

  proc {AddNewEvents JPIn NewSs Ens JPOut NewNs}
    case NewSs of S|Ss then JP2 NTail in
      NewNs = (JPIn.count+1)|NTail
      JP2 = {Record.adjoinList JPIn [
               count#NewNs.1
               events#{Record.adjoinAt JPIn.events NewC S}
               enablers#{Record.adjoinAt JPIn.enablers NewC Ens}
            ]}
      {AddNewEvents JP2 Ss Ens JPOut NTail}
    else JPOut=JPIn NewNs=nil end
  end

  proc {SetAsAlternatives JPIn Ns Ds JPOut}
    case Ns of N|NT then JP2 in
      JP2 = {Record.adjoinAt JPIn alternatives
                {Record.adjoinAt JPIn.alternatives N {List.append Ds NT}}}
      {SetAsAlternatives JP2 NT N|Ds JPOut}
    else JPIn = JPOut end
  end

  proc {AddIndistinguishableEvents JPIn NewNs JPOut}
    skip
  end

  %
  %  Assert that the given step exists with seqnum N in the execution.
  %  This is an analogue to {Insert} but instead of adding  new steps,
  %  it verifies an existing step.
  %
  proc {Assert JP N S Preceeds}
    skip
  end

  %
  %  Insert special 'finish' action in the run ending at N.
  %
  proc {Finish JPIn N JPOut}
    skip
  end

  %
  %  Determine the next-oldest events in the execution that do not
  %  conflict with event N.  This is always a list: it is nil if all
  %  more recent events conflict with N, or a list of alternatives otherwise.
  %
  proc {NextEvents JP N Ns}
    skip
  end

end
