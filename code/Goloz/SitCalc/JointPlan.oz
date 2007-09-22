%
%  JointPlan.oz:  build and maniplate joint plans
%
%  A joint plan is a map from agents to simplified program structures
%  consisting of the following operators:
%      nil   seq(Action Plan)  obs(Obs Plan Plan)
%

functor

import

  MSet at '../Utils/MSet.ozf'
  SitCalc
  Execution

export

  FromExs
  FromEx

define

    proc {EnsureObs JPBase Obs JPt}
       if {IsFree JPBase} then
         JPBase = obs(Obs JPt _)
       else JPt2 JPf Obs2 in
         JPBase = obs(Obs2 JPt2 JPf)
         if Obs2 == Obs then JPt = JPt2
         else {EnsureObs JPf Obs JPt} end
       end
    end


    proc {FromExs Exs JP}
       case Exs of E|Es then
         {FromEx E JP _}
         {FromExs Es JP}
       else 
         for Agt in {Record.arity JP} do
           {Closeoff JP.Agt}
         end
       end
    end

    %
    %  Build a joint plan from an execution.  JPBase is the entire
    %  joint plan being built, and JPHead is the head of the plan at
    %  the given execution.  It will always map each agent to either
    %  a free variable (they've just performed an action) or an obs()
    %  term (they make an observation at this point).
    %
    proc {FromEx E JPBase JPHead}
      JPHead = {SitCalc.newAgentMap}
      case E of ex(Step E2) then
        JPTail = {FromEx E2 JPBase}
        JPStep = {SitCalc.newAgentMap} in
        for Agt in {Record.arity JPTail} do MyActs MyObs in
          MyActs = for collect:C Actn in Step.action do
                     if {SitCalc.actor Actn} == Agt then {C Actn} end
                   end
          if MyActs \= nil then
            JPTail.Agt = seq(Step.action JPStep.Agt)
          else
            JPTail.Agt = JPStep.Agt
          end
          MyObs = {Value.condSelect Step.obs Agt nil}
          if MyObs \= nil then
            {EnsureObs JPStep.Agt MyObs JPHead.Agt}
          else
            JPHead.Agt = JPStep.Agt
          end
        end
      else JPHead = JPBase end
    end

    proc {Closeoff JP}
      if {IsFree JP} then
        JP = nil
      else
        case JP of seq(_ JP2) then {Closeoff JP2}
        []   obs(_ JP1 JP2) then {Closeoff JP1} {Closeoff JP2}
        end
      end
    end

end
