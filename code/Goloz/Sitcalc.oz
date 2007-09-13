%
%  Sitcalc.oz:  fundamental datastructures and code for reasoning in
%               the situation calculus.
%
%  This functor implements domain-independent functionality for reasoning
%  in the situation calculus.  Whenever it needs domain-specific information
%  it requests this from a sibling functor called "Domain".
%
%  We provide the following new notions over the basic sitcalc:
%
%    Step:    a step is an action that tracks some additional metadata
%             about what happened and why.  It pairs a (concurrent) action
%             with the following information:
%                 - test:  additional conditions that held before the action
%                 - thred: indicates which thred of execution the action
%                          was performed in service of
%                 - obs: indicates the observations made as a result of
%                        that action
%
%    Execution:  an execution is like a situation, but tracks steps rather
%                than just actions.  It is formed either by the special
%                situation term 'now' or an execution term ex(Step Ex).
%
%    CondPlan:   a conditional plan for execution.  This is a simplified
%                MIndiGolog program containing only the following operators:
%                    nil   seq(A CP)  obs(Obs CPt CPf)
%
%    JointPlan:  a mapping from agents to conditional plans.  The point of
%                planning is to produce a shared JointPlan that can then be
%                executed without further delibaration.
%

functor

import

  LP
  Domain

  Module

export

  Actor

  Uniformize
  Regress

  Ex
  Jplan

define

  %
  %  Create our private FOF reasoning module.
  %  We delegate determination of WFF to the Domain module.
  %
  FOF = _
  {Module.link ['FOF.ozf'] [FOF]}
  FOF.lang = lang(
    wff: proc {$ P}
           % TODO: ensure well-formedness of predicates
           skip
         end
    assign: proc {$ Vs}
           % TODO: assign values to free variables
           skip
         end
  )

  %
  %  Extract the actor from a given action.
  %  Fails if the action is exogenous.
  %
  proc {Actor Actn Agt}
    {LP.neg proc {$} {Domain.natural Actn} end}
    Agt = Actn.1
  end

  %
  %  Flatten defined fluents according to their definitions in the domain
  %
  Uniformize = {FOF.transformation 'sitcalc.uniformize' Uniformize_atom}
  proc {Uniformize_atom P U}
    U = {FOF.atom P}
  end

  %
  %  Regress the formula over the given action.
  %
  Regress = {FOF.transformation 'sitcalc.regress' Regress_atom}
  proc {Regress_atom P A U}
    EpsP EpsN
  in
    EpsP = {Domain.causes_true A P}
    EpsN = {Domain.causes_false A P}
    U = {FOF.simplify {FOF.parseRecord 'or'(EpsP and(P neg(EpsN)))}}
  end

  %
  %  Determine whether the given formula holds in the given
  %  situation.
  %
  proc {Holds F S B}
    case S of res(C Sr) then Fr = {Regress F C} in B={Holds Fr Sr}
    else B={HoldsInit F}
    end
  end

  proc {HoldsInit F B}
    {FOF.tautology_e F _ B}
  end

  
  %
  %  Procedures for dealing with executions.
  %  An execution is like a situation with some extra metadata attached.
  %  It bottoms out in 'now' rather than s0.
  %
  Ex = ex(

    append: proc {$ EIn Step EOut}
              Test = {Value.condSelect Step test true}
              Act = {Value.condSelect Step action nil}
              Thred = {Value.condSelect Step thred nil}
              Obs = {Value.condSelect Step obs nil}
            in
              EOut = ex(step(test:Test action:Act thred:Thred obs:Obs) EIn)
            end

    addtest: proc {$ EIn C EOut}
              case EIn of ex(Step E2) then Step2 in
                Step2 = {Record.adjoinAt Step test and(C Step.test)}
                EOut = ex(Step2 E2)
              else
                EOut = {Ex.append EIn step(test: C)}
              end
             end

    addthred: proc {$ EIn T EOut}
                case EIn of ex(Step E2) then Step2 in
                  Step2 = {Record.adjoinAt Step thred T|Step.thred}
                  EOut = ex(Step2 E2)
                else EIn = EOut end
              end

    addobs: proc {$ EIn O EOut}
             case EIn of ex(Step E2) then Step2 in
               Step2 = {Record.adjoinAt Step obs O|Step.obs}
               EOut = ex(Step2 E2)
             else EIn = EOut end
            end

    %
    %  Generate the set of possible outcomes of the last step of E,
    %  returning a list of executions, one for each outcome.
    %  TODO: enumerating action outcomes, interacting with knowledge.
    %
    outcomes: proc {$ E Outcomes}
                Outcomes = [E]
              end

    %
    %  Determine whether two executions are indistinguishable from the
    %  point of view of a single agent.
    %
    matches: proc {$ E1 E2 Agt B}
               if E1 == now and E2 == now then B=true
               else  Obs1 Eo1 Obs2 Eo2 in
                 {Ex.unwindToObs E1 Agt Obs1 Eo1}
                 {Ex.unwindToObs E2 Agt Obs2 Eo2}
                 if Obs1 == Obs2 then
                   B = {Ex.matches {Ex.unwind E1} {Ex.unwind E2} Agt}
                 else B=false end
               end
             end


    %
    %  Unwind a step of the execution, or remain in 'now' if no steps.
    %  This is basically the opposite of {append}.
    %
    unwind: proc {$ EIn EOut}
              case EIn of ex(_ E2) then EOut = E2
              else EOut = EIn end
            end

    %
    %  Unwind to the last observation made by the given agent.
    %
    unwindToObs: proc{$ EIn Agt Obs EOut}
                   if EIn == now then Obs=nil EOut=now
                   else
                     Obs2 = {Ex.getobs EIn Agt}
                    in
                     if Obs2 == nil then
                       E2 = {Ex.unwind EIn}
                       {Ex.unwindToObs E2 Obs EOut}
                     else
                       Obs=Obs2 EOut=EIn
                     end
                   end
                 end

    %
    %  Get the observation made by the given agent during the last
    %  step of the execution.  May be nil.
    %
    getobs: proc {$ E Agt Obs}
              %TODO: Sitcalc.ex.getobs
              Obs = nil
            end

    %
    %  Determine whether F is known to hold after the execution of E.
    %  The definition of 'known' can be any knowledge operator for
    %  which we have an implementation, and which is equivalent across
    %  agents (e.g: distributed knowledge, common knowledge)
    %
    %  Note that since this is based on knowledge, there's no excluded
    %  middle - it's possible for holds(F E) and holds(neg(F) E) to both
    %  be false.
    %
    holds: proc {$ F E B}
             %TODO: Sitcalc.ex.holds
             B= true
           end

  )


  Jplan = jplan(

    finish: proc {$ JP}
              for CP in {Record.toList JP} do
                CP = nil
              end
            end

    extend: proc {$ JP E Branches}
              Outcomes = {Ex.outcomes E}
            in
              if {List.length Outcomes} == 1 then
                JP2 = {Jplan.addstep JP E} in
                Branches = [E#JP2]
              else
                {Jplan.extendRec JP Outcomes Branches}
              end
            end

    extendRec: proc {$ JP Outcomes Branches}
                 case Outcomes of E|Es then JPt JPf B2 in
                   {Jplan.addobs JP E JPt JPf}
                   Branches = E#JPt|B2
                   {Jplan.extendRec JPf Es B2}
                 else
                   {Jplan.finish JP}
                   Branches = nil
                 end
               end

    addstep: proc {$ JP E JPOut}
               JPOut = {Record.clone JP}
               %TODO: Sitcalc.jplan.addstep on per-agent basis
               for Agt in {Record.arity JP} do
                 JP.Agt = seq(E.1.action JPOut.Agt)
               end
             end

    addobs: proc {$ JP E JPt JPf}
              %TODO: Sitcalc.jplan.addobs
              skip
            end

  )
  
end

