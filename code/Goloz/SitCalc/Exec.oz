%
%  Execution.oz
%
%  Implements an execution, a partial order of steps.
%


functor

import

  LP at '../Utils/LP.ozf'
  MList at '../Utils/MList.ozf'
  SitCalc

export

  Init
  Insert
  Outcomes

  Holds
  HoldsFOF
  HoldsW

define

  %
  %  Initialize a new (empty) execution.
  %  Its history and future are both initially empty.
  %
  proc {Init Ex}
    Ex = ex(count: 0
           past: nil
           future: nil
           after: nil)
  end

  %
  %  Insert a new step into the execution.
  %
  proc {Insert ExIn Step ExOut}
    COut FOut AOut IsAfter
  in
    ExOut = ex(count:COut past:ExIn.past future:FOut after:AOut)
    COut = ExIn.count + 1
    FOut = (COut#E)|ExOut.future
    IsAfter = {MList.new}
    for (C2#S2) in ExIn.future do
          if {EventIsFree ExIn C2 {MList.toList IsAfter}} then
            if {OrderedAfter Step S2} then 
              {MList.cons Ordered C2}
            end
          end
    end
    AOut = {Record.adjoinAt ExIn.after COut {MList.toList IsAfter}}
  end

  proc {OrderedAfter E1 E2 B}
    CanNo = {Step.canBeConc E1 E2}
    CanYes = for return:R default:true Agt in E1.action do
               if {Step.getobs E2 Agt} == nil then
                 {R false}
               end
             end
  in
    if CanYes then
      if CanNo then
        choice B=true [] B=false end
      else
        B = true
      end
    elseif CanNo then
      B = false
    else fail end
  end

  proc {EventIsFree Ex C Cs B}
    case Cs of C2|C2s then
      if {List.member C Ex.after.C2} then B=false
      else
        B = {EventIsFree C {List.append C2s Ex.after.C2}}
      end
    else B = true end
  end

  %
  %  Step the execution forward one event.  This generates
  %  a list of executions, each of which are one possible
  %  evolution of the input execution.
  %
  proc {NextSteps ExIn ExOuts}
    FreeSteps={List.filter {Record.toListInd ExIn.after} fun{$ S}(S.2==nil)end}
  in
    {NextSteps_rec ExIn FreeSteps ExOuts}
  end

  proc {NextSteps_rec ExIn Steps ExOuts}
    case Steps of S|Ss then ExOuts2 in
      ExOuts = {DoStep ExIn S}|ExOuts2
      {NextSteps_rec ExIn Ss ExOuts2}
    else ExOuts = nil end
  end

  %
  %  Move the execution forward by the given step (an ID#Step pair)
  %
  proc {DoStep ExIn S ExOut}
    OPast OFuture OAfter1 OAfter
  in
    ExOut = ex(count: ExIn.count past:OPast future:OFuture after:OAfter)
    OAfter1 = {Record.subtract ExIn.after S.1}
    OAfter = {Record.map OAfter1 fun {$ L} {List.subtract L S.1} end}
    OFuture = {List.subtract ExIn.future S}
    OPast = S|ExIn.past
  end

  %
  %  Generate the set of possible outcomes of the last step inserted
  %  into E, returning a list of executions, one for each outcome.
  %  This basically involves enumerating the possible observations for
  %  each agent and each action.
  %
  proc {Outcomes E Es}
    case E.future of (C#S)|_ then
      {OutcomesActs E S.action Es}
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
          for Res#Cond in AOuts do
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

  proc {Addobs ExIn Obs ExOut}
    S2 = {Step.addobs ExIn.future.1.2 Obs}
  in
    ExOut = {Record.adjoinAt ExIn future S2|ExIn.future.2}
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

  proc {HoldsW_FOF E FIn Res}
    F = {SitCalc.uniformize FIn}
    Res2
  in
    case E of ex(Step E2) then
      Res2 = {SitCalc.fof.tautOrCont {SitCalc.fof.impl SitCalc.axioms F}}
      if Res2 == taut then Res = yes
      elseif Res2 == cont then Res = no
      else FmlR in
        %TODO: include observations in regression for HoldsW_FOF
        FmlR = {SitCalc.regress F Step.action}
        {HoldsW_FOF E2 FmlR Res}
      end
    else
      Axioms = {SitCalc.fof.conj SitCalc.initially SitCalc.axioms} in
      Res2 = {SitCalc.fof.tautOrCont {SitCalc.fof.impl Axioms F}}
      if Res2 == taut then Res = yes
      elseif Res2 == cont then Res = no
      else Res = unknown end
    end
  end

end
