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
%                        that action, indexed by agent
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

  Module

export

  Actor
  Regress

  Ex
  Jplan

  Test

define

  %
  %  Create our private FOF reasoning module.
  %  We delegate determination of WFF to the Domain module.
  %
  FOF = _
  {Module.link ['FOF/FOF.ozf'] [FOF]}
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
  %  Make a private DomainBuilder, and import definitions from Domain.oz
  %  We'll pass all domain-dependant queries to DB.query
  %
  DB = _
  {Module.link ['DomainBuilder.ozf' 'Domain.ozf'] [DB _]}


  %
  %  Extract the actor from a given action.
  %
  proc {Actor Actn Agt}
    Agt = Actn.1
  end

  %
  %  Regress the formula over the given action.
  %
  proc {Regress_atom P A U}
    EpsP EpsN
  in
    EpsP = {DB.query.causesTrue P A}
    EpsN = {DB.query.causesFalse P A}
    U = {FOF.simplify {FOF.parseRecord 'or'(EpsP and(P neg(EpsN)))}}
  end
  Regress = {FOF.transformation 'sitcalc.regress' Regress_atom}


  proc {NewAgentMap M}
    names = {DB.query.agents} in
    M = {Record.adjoinList agtmap {List.map names fun {$ E} E#_ end}}
  end

  proc {ActionOutcomes Act Outcomes}
    %TODO: Sitcalc.actionOutcomes
    Outcomes = nil
  end 
  
  %
  %  Procedures for dealing with executions.
  %  An execution is like a situation with some extra metadata attached.
  %  It bottoms out in 'now' rather than s0.
  %
  Ex = ex(

    %
    %  Add a new step to the execution.  Any fields in the step that
    %  are not specified will be given a suitable default value.
    %
    append: proc {$ EIn Step EOut}
              Test = {Value.condSelect Step test true}
              Act = {Value.condSelect Step action nil}
              Thred = {Value.condSelect Step thred nil}
              Obs = {Value.condSelect Step obs nil}
            in
              EOut = ex(step(test:Test action:Act thred:Thred obs:Obs) EIn)
            end

    %
    %  Add an additional test condition to the latest step of execution.
    %
    addtest: proc {$ EIn C EOut}
              case EIn of ex(Step E2) then Step2 in
                Step2 = {Record.adjoinAt Step test and(C Step.test)}
                EOut = ex(Step2 E2)
              else
                EOut = {Ex.append EIn step(test: C)}
              end
             end

    %
    %  Push an additional thread identifier for the latest step of execution
    %
    addthred: proc {$ EIn T EOut}
                case EIn of ex(Step E2) then Step2 in
                  Step2 = {Record.adjoinAt Step thred T|Step.thred}
                  EOut = ex(Step2 E2)
                else EIn = EOut end
              end

    %
    %  Add some observations to the latest step of the execution.
    %  O is expected to be a map from agents to the observations they
    %  have made.
    %
    addobs: proc {$ EIn O EOut}
             case EIn of ex(Step E2) then Step2 O2 in
               O2 = {NewAgentMap}
               for Agt in {Record.arity O2} do
                 O2.Agt = {List.append {Value.condSelect O Agt nil}
                                       {Value.condSelect Step.obs Agt nil}}
               end
               Step2 = {Record.adjoinAt Step obs O2}
               EOut = ex(Step2 E2)
             else EIn = EOut end
            end

    %
    %  Generate the set of possible outcomes of the last step of E,
    %  returning a list of executions, one for each outcome. This
    %  basically involves enumerating the possible observations for
    %  each agent and each action.
    %
    outcomes: proc {$ E Outcomes}
                case E of ex(Step _) then
                  {Ex.outcomesActs E Step.action Outcomes}
                else Outcomes = [E] end
              end

    outcomesActs: proc {$ E Actions Outcomes}
                    case Actions of A|As then OutA in
                      OutA = {Ex.outcomesAgts E A {DB.query.agents}}
                      Outcomes = for append:A ExA in OutA do
                                   {A {Ex.outcomesActs ExA As}}
                                 end
                    else
                      Outcomes = [E]
                    end
                  end

    %
    %  Enumerate outcome executions for a single action for each agent
    %
    outcomesAgts: proc {$ E Act Agents Outcomes}
                    case Agents of Agt|As then OutA in
                      OutA = {Ex.outcomesAA E Act Agt}
                      Outcomes = for append:A ExA in OutA do
                                   {A {Ex.outcomesAgts ExA Act As}}
                                 end
                    else
                      Outcomes = nil
                    end
                  end

    %
    %  Enumerate outcome executions for the given (single) action and Agent.
    %
    outcomesAA: proc {$ E Act Agt Outcomes}
                  CanObs = {Ex.holdsW E canObs(Agt Act)}
                in
                  if CanObs == no then
                    Outcomes = [E]
                  else
                    Acc = {LP.listAcc Outcomes}
                    CanSense = {Ex.holdsW E canSense(Agt Act)} 
                   in
                    if CanObs == unknown then
                      {Acc E}
                    end
                    if CanSense \= yes then
                      {Acc {Ex.addobs E o(Agt: Act)}}
                    end
                    if CanSense \= no then
                      for Res#Cond in {ActionOutcomes Act} do
                        if {Ex.holds E neg(Cond)} then skip
                        else {Acc {Ex.addobs E o(Agt: Act#Res)}} end
                      end
                    end
                    {Acc nil}
                  end
                end

    %
    %  Determine whether F is known to hold after the execution of E.
    %  The definition of 'known' can be any knowledge operator for
    %  which we have an implementation, and which is equivalent across
    %  agents (e.g: dknows, sknows, cknows)
    %
    %  Note that since this is based on knowledge, there's no excluded
    %  middle - it's possible for holds(F E) and holds(neg(F) E) to both
    %  be false.
    %
    holds: proc {$ F E B}
             %TODO: Sitcalc.ex.holds
             B = true
           end

    %
    %  Determine if it is known whether F holds after the execution of E.
    %  Unlike Ex.holds, this procedure returns one of 'yes', 'no' or 
    %  'unkown'.
    %
    holdsW: proc{$ F E Res}
              if {Ex.holds F E} then
                Res = yes
              else
                if {Ex.holds neg(F) E} then
                  Res = no
                else
                  Res = unkown
                end
              end
            end

    %
    %  Lazily produces the list of actions corresponding to the given
    %  execution, most recent action first.
    %
    actions: fun lazy {$ E}
               case E of ex(S E2) then
                 if S.action == nil then {Ex.actions E2}
                 else (S.action)|{Ex.actions E2} end
               else nil end
             end

    %
    %  Get the observation made by the given agent during the last
    %  step of the execution.  May be nil.
    %
    getobs: proc {$ E Agt Obs}
              case E of ex(Step _) then
                if Step.obs == nil then Obs = nil
                else Obs = {Value.condSelect Step.obs Agt nil} end
              else Obs = nil end
            end

    %
    %  Lazily produces the list of observations made by the given agent
    %  during the given observation, most recent observation first.
    %
    observations: fun lazy {$ E Agt}
                    case E of ex(S E2) then
                      O = if S.obs==nil then nil
                          else {Value.condSelect S.obs Agt nil} end
                     in
                      if O == nil then {Ex.observations E2 Agt}
                      else (O)|{Ex.observations E2 Agt} end
                    else nil end
                  end


  )


  Jplan = jplan(

    init: proc {$ JP}
            JP = {NewAgentMap}
          end

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


  proc {Test}
    {Test_ex}
  end


  proc {Test_ex}
    E1 E2 E3 E4 E5 E6 E7
  in
    E1 = {Ex.append now step(test: p(a b))}
    E1.1.obs = nil
    E1.1.action = nil
    E1.1.thred = nil
    E2 = {Ex.append E1 step(action: drop(a))}
    E2.1.action = drop(a)
    E2.2 = E1
    E3 = {Ex.addtest E2 q(b a)}
    E3.1.test = and(q(b a) true)
    E4 = {Ex.addthred {Ex.addthred E3 1} 0}
    E4.1.thred = [0 1]
    {Ex.observations E1 thomas} = {Ex.observations E2 thomas}
    {Ex.observations E1 thomas} = {Ex.observations E3 thomas}
    E5 = {Ex.addobs E4 o(thomas: [o1 o2])}
    {Ex.getobs E5 thomas [o1 o2]}
    E6 = {Ex.addobs E5 o(thomas: [o3])}
    {Ex.getobs E6 thomas [o3 o1 o2]}
    false=({Ex.observations E5 thomas} == {Ex.observations E4 thomas})
    false=({Ex.observations E5 thomas} == {Ex.observations E6 thomas})
    E7 = {Ex.addobs E1 o(thomas: [o3 o1 o2])}
    {Ex.observations E6 thomas} = {Ex.observations E7 thomas}
  end
  
end

