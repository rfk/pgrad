%
%  Execution.oz:  procedures for building and manipulating executions
%
%  An execution is like a situation, but tracks 'steps' rather than just
%  actions.  It is formed either by the special situation term 'now' or
%  and execution term ex(Step Ex).
%
%  A step tracks additional metadata about what actions were performed
%  and why.  It pairs a (concurrent) action with the following info:
%      - test:  additional conditions that held befor the action
%      - thred: indicates the thred of execution the action was performed
%               in service of
%      - obs:   indicates the observations made by each agent as a result
%               of performing the action.
%
%  An execution is said to be 'valid' if the sequences of actions and
%  observations made by each agent can be interleaved in any way without
%  disturbing the following invariants:
%      - all test conditions continue to hold prior to the corresponding action
%      - actions with a common thred prefix maintain their relative order
%
%  The functions in this module refuse to construct invalid executions,
%  failing instead.
%

functor

import

  LP at '../LP.ozf'
  MSet at '../Utils/MSet.ozf'
  SitCalc

  Search

export

  Append
  Addtest
  Addthred
  Addobs
  Outcomes
  Actions
  Observations

  Holds
  HoldsFOF
  HoldsW

  Test

define

    %
    %  Add a new step to the execution.  Any fields in the step that
    %  are not specified will be given a suitable default value.
    %
    proc {Append EIn Step EOut}
      Test = {Value.condSelect Step test true}
      ActT = {Value.condSelect Step action nil}
      Act = if {List.is ActT} then ActT else [ActT] end
      Thred = {Value.condSelect Step thred nil}
      Obs = {Value.condSelect Step obs nil}
    in
      EOut = ex(step(test:Test action:Act thred:Thred obs:Obs) EIn)
    end

    %
    %  Add an additional test condition to the latest step of execution.
    %
    proc {Addtest EIn C EOut}
      case EIn of ex(Step E2) then Step2 in
        Step2 = {Record.adjoinAt Step test and(C Step.test)}
        EOut = ex(Step2 E2)
      else
        EOut = {Append EIn step(test: C)}
      end
    end

    %
    %  Push an additional thread identifier for the latest step of execution
    %
    proc {Addthred EIn T EOut}
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
    proc {Addobs EIn O EOut}
      case EIn of ex(Step E2) then Step2 O2 in
        O2 = {SitCalc.newAgentMap}
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
    proc {Outcomes E Es}
      case E of ex(Step _) then
        {OutcomesActs E Step.action Es}
      else Es = [E] end
    end

    proc {OutcomesActs E Actions Outcomes}
        case Actions of A|As then OutA in
          OutA = {OutcomesAgts E A {SitCalc.agents}}
          Outcomes = for append:A ExA in OutA do
                       {A {OutcomesActs ExA As}}
                     end
        else
          Outcomes = [E]
        end
    end

    proc {OutcomesAgts E Act Agents Outcomes}
      case Agents of Agt|As then OutA in
        OutA = {OutcomesAA E Act Agt}
        Outcomes = for append:A ExA in OutA do
                     {A {OutcomesAgts ExA Act As}}
                   end
      else
        Outcomes = [E]
      end
    end

    %
    %  Enumerate outcome executions for the given (single) action and agent.
    %
    proc {OutcomesAA E Act Agt Outcomes}
      CanObs = {HoldsW E canObs(Agt Act)}
    in
      if CanObs == no then
        Outcomes = [E]
      else
        Acc = {LP.listAcc Outcomes}
        CanSense = {HoldsW E canSense(Agt Act)} 
       in
        if CanObs == unknown then
          {Acc E}
        end
        if CanSense \= yes then
          {Acc {Addobs E o(Agt: [Act])}}
        end
        if CanSense \= no then
          AOuts = {SitCalc.actionOutcomes Act} in
          if AOuts == nil then
            {Acc {Addobs E o(Agt: [Act])}}
          else 
            for Res#Cond in {SitCalc.actionOutcomes Act} do
              _={LP.ifNot proc {$ R}
                             {Holds E neg(Cond)}
                          end
                          proc {$ R}
                             {Acc {Addobs E o(Agt: [Act#Res])}}
                          end}
            end
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
    %  Designed to be used during program search, so it's an assertion
    %  rather than a function, and will bind variables in F to ensure that
    %  it holds.
    %
    proc {Holds E F}
      Fml Binder Binding
    in
      Fml = {SitCalc.fof.parseRecord F Binder}
      Binding = {HoldsFOF E Fml}
      {Binder Binding}
    end

    proc {HoldsFOF E FmlIn Bind}
      Fml = {SitCalc.uniformize FmlIn}
    in
      case E of ex(Step E2) then
       if {SitCalc.fof.contradiction {SitCalc.fof.impl SitCalc.axioms Fml}} then
         fail
       else FmlR in
         %TODO: include observations in regression for holdsFOF
         FmlR = {SitCalc.regress Fml Step.action}
         {HoldsFOF E2 FmlR Bind}
       end
      else
        Axioms = {SitCalc.fof.conj SitCalc.axioms SitCalc.initially} in
        {SitCalc.fof.prove {SitCalc.fof.impl Axioms Fml} Bind}
      end
    end

    %
    %  Determine if it is known whether F holds after the execution of E.
    %  Unlike {Holds}, this procedure returns one of 'yes', 'no' or 
    %  'unknown' and will not bind free variables.
    %
    proc {HoldsW E F Res}
      Fml = {SitCalc.fof.parseRecord F _}
    in
      Res = {HoldsW_FOF E Fml}
    end

    proc {HoldsW_FOF E F Res}
      Res2
    in
      case E of ex(Step E2) then
        Res2 = {SitCalc.fof.tautOrCond {SitCalc.fof.impl SitCalc.axioms F}}
        if Res2 == taut then Res = yes
        elseif Res2 == cont then Res = no
        else FmlR in
          %TODO: include observations in regression for HoldsW_FOF
          FmlR = {SitCalc.regress F Step.action}
          {HoldsW_FOF E2 FmlR Res}
        end
      else
        Axioms = {SitCalc.fof.conj SitCalc.initially SitCalc.axioms} in
        Res2 = {SitCalc.fof.tautOrCond {SitCalc.fof.impl Axioms F}}
        if Res2 == taut then Res = yes
        elseif Res2 == cont then Res = no
        else Res = unknown end
      end
    end

    %
    %  Lazily produces the list of actions corresponding to the given
    %  execution, most recent action first.
    %
    fun lazy {Actions E}
      case E of ex(S E2) then
        if S.action == nil then {Actions E2}
        else (S.action)|{Actions E2} end
      else nil end
    end

    %
    %  Get the observation made by the given agent during the last
    %  step of the execution.  May be nil.
    %
    proc {Getobs E Agt Obs}
      case E of ex(Step _) then
        if Step.obs == nil then Obs = nil
        else Obs = {Value.condSelect Step.obs Agt nil} end
      else Obs = nil end
    end

    %
    %  Lazily produces the list of observations made by the given agent
    %  during the given observation, most recent observation first.
    %
    fun lazy {Observations E Agt}
      case E of ex(S E2) then
         O = if S.obs==nil then nil
             else {Value.condSelect S.obs Agt nil} end
        in
         if O == nil then {Observations E2 Agt}
        else (O)|{Observations E2 Agt} end
      else nil end
    end


  proc {Test}
    E1 E2 E3 E4 E5 E6 E7
  in
    E1 = {Append now step(test: p(a b))}
    E1.1.obs = nil
    E1.1.action = nil
    E1.1.thred = nil
    E2 = {Append E1 step(action: drop(a))}
    E2.1.action = [drop(a)]
    E2.2 = E1
    E3 = {Addtest E2 q(b a)}
    E3.1.test = and(q(b a) true)
    E4 = {Addthred {Addthred E3 1} 0}
    E4.1.thred = [0 1]
    {Observations E1 thomas} = {Observations E2 thomas}
    {Observations E1 thomas} = {Observations E3 thomas}
    E5 = {Addobs E4 o(thomas: [o1 o2])}
    {Getobs E5 thomas [o1 o2]}
    E6 = {Addobs E5 o(thomas: [o3])}
    {Getobs E6 thomas [o3 o1 o2]}
    false=({Observations E5 thomas} == {Observations E4 thomas})
    false=({Observations E5 thomas} == {Observations E6 thomas})
    E7 = {Addobs E1 o(thomas: [o3 o1 o2])}
    {Observations E6 thomas} = {Observations E7 thomas}

    {Search.base.one proc {$ R} {Holds E7 true} R=unit end} = [_]
    {Search.base.one proc {$ R} {Holds E4 false} R=unit end} = nil
  end
  
end

