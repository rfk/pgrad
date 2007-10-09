%
%  Planner.oz:  planning stuff for MIndiGolog
%

functor 

import

  LP at '../Utils/LP.ozf'
  SitCalc
  Exec
  Step

export

  JointPlan

define

  %
  %  Search for a join plan executing program D in the current situation.
  %  To do so, construct a closed PlanFront starting from now#D
  %
  proc {JointPlan D E}
    {MakeJointPlan {Exec.init} [D#{Map.init}#0] E}
  end

  %
  %  Construct a joint execution, one step at a time, one branch at a time.
  %  EIn is the execution constructed so far.
  %  Branches is a list of D#M#B tuples, where B is the branch identifier,
  %  D is the program remaining to be executed, and M is branch-specific
  %  metadata about events.
  %
  proc {MakeJointExec EIn Branches EOut}
    case Branches of (D1#M1#B1)|Bs then
      (D#M#B)|NewBs = {ConsumeExistingEvents EIn D1#M1#B1} in
      choice  {Final D {Exec.toSituation EIn B}} then E2 in
           E2 = {Exec.finish EIn B}
           {MakeJointExec E2 {List.append NewBs Bs} EOut}
      [] D2 E2 M2 S Outcomes in
           {Trans D {Exec.toSituation EIn B} D2 S}
           Outcomes = for collect:C B2 in {Exec.insert EIn S E2} do
                       {C D2#{Map.set M B2.1 S}#B2}
                      end
           {MakeJointExec E2 {List.append Outcomes {List.append NewBs Bs}} EOut}
      end
    else EOut = EIn end
  end

  %
  %  Transition the program D (that remains on branch B) to account for
  %  any events on its branch that were inserted after B.  This ensures
  %  that its execution is compatible with those of existing branches.
  %  Returns a list of D#M#B tuples.
  %
  proc {ConsumeExistingEvents E D#M#B Branches}
    B2s = {Exec.nextEvents B}
  in
    if B2s == nil then
      Branches = [D#M#B]
    else
      Branches=for collect:C B2 in B2s do D2 S in
                 {Trans D {Exec.toSituation E B2} D2 S}
                 S.action = {Exec.getAction B2.1}
                 {Ex.assert E S
                 {C D2#}
               end
    end
  end

  proc {Trans1 D E Dp Steps}
    Dr Sr
  in
    {Trans D E Dr Sr}
    if Sr.action == nil then skip
    else skip
    end
  end
  
  proc {Test}
    skip
  end

end
