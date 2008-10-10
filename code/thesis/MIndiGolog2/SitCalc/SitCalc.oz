%
%  Sitcalc.oz:  fundamental datastructures and code for reasoning in
%               the situation calculus.
%
%  This functor implements domain-independent functionality for reasoning
%  in the situation calculus.  Whenever it needs domain-specific information
%  it requests this from a sibling functor called "Domain".
%

functor

import

  MSet at '../Utils/MSet.ozf'
  LP at '../Utils/LP.ozf'
  Step

  Module
  Search
  System

export

  Actor
  Actors
  Agents
  Uniformize
  Regress
  ActionOutcomes
  Outcomes
  NewAgentMap
  IndependentActs

  Holds
  HoldsW

  ShowRun
  Test 

define

  %
  %  Create our private FOF reasoning module.
  %  We delegate determination of WFF to the Domain module.
  %
  FOF = _
  {Module.link ['/storage/uni/pgrad/code/thesis/MIndiGolog2/FOF/FOF.ozf'] [FOF]}
  FOF.lang = lang(
    wfp: proc {$ P}
            {DB.query.wfp P}
         end
    assign: proc {$ Vs}
           for V in Vs do
             {DB.query.assign V}
           end
         end
  )

  %
  %  Make a private DomainBuilder, and import definitions from Domain.oz
  %  We'll pass all domain-dependant queries to DB.query
  %
  DB = _
  Domain = _
  {Module.link ['/storage/uni/pgrad/code/thesis/MIndiGolog2/SitCalc/DomainBuilder.ozf' '/storage/uni/pgrad/code/thesis/MIndiGolog2/Domain.ozf'] [DB Domain]}
  % Ensure that Domain module is loaded
  {Wait Domain}


  %
  %  Extract the actor from a given action.
  %
  proc {Actor Actn Agt}
    Agt = Actn.1
  end

  %
  %  Get the actors involved in a given complex action
  %
  proc {Actors Actns Agts}
    AgtsM = {MSet.new}
  in
    for Actn in Actns do
      {MSet.insert AgtsM {Actor Actn}}
    end
    Agts = {MSet.toList AgtsM}
  end

  proc {IndependentActs A1 A2 B}
    if {Actor A1} == {Actor A2} then B = false
    elseif {Record.label A1} == check_for_eggs then
        if {Record.label A2} \= acquire then B = true
        else B = (A1.2 \= {Record.label A2.2}) end
    else B = for return:R default:true Arg1 in {Record.toList A1} do
               for Arg2 in {Record.toList A2} do
                 if Arg2 == Arg1 then {R false} end
               end
             end
    end
  end

  proc {Agents Agts}
    {DB.query.agents Agts}
  end

  %
  %  Regress the formula over the given action.
  %
  proc {Regress_atom P A U}
    EpsP EpsN
  in
    EpsP = {DB.query.causesTrue P A}
    EpsN = {DB.query.causesFalse P A}
    U = 'or'(EpsP and(P neg(EpsN)))
  end

  proc {Regress F A R}
    TF = {FOF.transformFunc fun {$ Atom} {Regress_atom Atom A} end}
  in
    R = {TF F}
  end

  %
  %  Uniformize the given formula
  %
  proc {Uniformize_atom P U}
    Defn
  in
    Defn = {DB.query.adfluent P}
    if Defn \= nil then U = {Uniformize Defn}
    else Defn in
       Defn = {DB.query.builtin P}
       if Defn \= nil then U = {Uniformize Defn}
       else U = P end
    end
  end

  Uniformize = {FOF.transformFunc Uniformize_atom}

  %
  %  Create a record mapping each agent name to a fresh variable.
  %
  proc {NewAgentMap M}
    Names = {DB.query.agents} in
    M = {Record.adjoinList agtmap {List.map Names fun {$ E} E#_ end}}
  end

  proc {ActionOutcomes Act Outcomes}
    Outcomes = {DB.query.outcomes Act}
  end 

  %
  %  Return a list of steps, one for each possible outcome of the
  %  step S.  This involves enumerating the different possible combinations
  %  of observations made by each agent.
  %
  proc {Outcomes R S Outs}
    MyS = {Record.adjoinAt S obs {NewAgentMap}}
  in
    Outs = {OutcomesAgts R [MyS] {Record.arity MyS.obs}}
  end

  proc {OutcomesAgts R Steps Agts Outs}
    case Agts of Agt|As then NewSteps in
      NewSteps = for append:Acc S in Steps do
                {Acc {OutcomesAgt R S Agt}}
              end
      {OutcomesAgts R NewSteps As Outs}
    else Outs = Steps end
  end

  proc {OutcomesAgt R S Agt Outs}
    % TODO: SitCalc.OutcomesAgt: take into account existing obs on the step
    CanObs = {HoldsW R canObs(Agt S.action)}
  in
    if CanObs == no then
      Outs = [{Step.setobs S Agt nil}]
    else
      Acc = {LP.listAcc Outs}
      CanSense = {HoldsW R canSense(Agt S.action)}
     in
      if CanObs == unknown then
        {Acc {Step.setobs S Agt nil}}
      end
      if CanSense \= yes then
        {Acc {Step.setobs S Agt S.action}}
      end
      if CanSense \= no then
        AOuts = {ActionOutcomes S.action} in
        if AOuts == nil then
          {Acc {Step.setobs S Agt S.action}}
        else
         for Res#Cond in AOuts do
            if {HoldsW R Cond} \= no then
               {Acc {Step.setobs S Agt S.action#Res}}
            end
          end
        end
      end
      {Acc nil}
    end
  end

  Initially = {Uniformize {List.toTuple and {DB.query.initially}}}

  %
  %  Determine whether F is known to hold after the run of execution R.
  %
  %  Designed to be used during program search, so it's an assertion
  %  rather than a function, and will bind variables in F to ensure that
  %  it holds.
  %
  proc {Holds R FmlIn}
    Fml = {Uniformize FmlIn}
  in
    case R of ex(Step R2) then
       if Step.action \= nil then ObsFmls ObsFml FmlR in
         ObsFmls = for collect:C Agt in {Record.arity Step.obs} do
           {C {ObsImplies Agt Step.action Step.obs.Agt}}
         end
         ObsFml = {Uniformize {List.toTuple and true|ObsFmls}}
         FmlR = {Regress impl(ObsFml Fml) Step.action}
         {Holds R2 {FOF.simplify FmlR}}
       else
         {Holds R2 Fml}
       end
     end
    else
      {FOF.tautology impl(Initially Fml)}
    end
  end

  proc {ObsImplies Agt Act Obs Fml}
    case Obs of Act#Out then
      Fml = for return:R default:false Res#Cond in {ActionOutcomes Act} do
              if Out == Res then
                {R and(canObs(Agt Act) canSense(Agt Act) Cond)}
              end
            end
    [] nil then Fml = neg(canObs(Agt Act))
    else Fml = and(canObs(Agt Act) neg(canSense(Agt Act))) end
  end

  %
  %  Determine if it is known whether F holds after the run of execution R.
  %  Unlike {Holds}, this procedure returns one of 'yes', 'no' or
  %  'unknown' and will not bind free variables.
  %
  proc {HoldsW R FIn Res}
    F = {Uniformize FIn}
  in
    case R of ex(Step R2) then
      if Step.action \= nil then ObsFmls ObsFml FmlR in
        ObsFmls = for collect:C Agt in {Record.arity Step.obs} do
          {C {ObsImplies Agt Step.action Step.obs.Agt}}
        end
        ObsFml = {Uniformize {List.toTuple and true|ObsFmls}}
        FmlR = {Regress impl(ObsFml F) Step.action}
        {HoldsW R2 FmlR Res}
      else
        {HoldsW R2 F Res}
      end
    else
      if {FOF.tautology impl(Initially F)} then
        Res = yes
      else
        if {FOF.contradiction and(Initially F)} then
          Res = no
        else
          Res = unknown
        end
      end
    end
  end


  proc {Test}
    F1 F2 F3
  in
    {HoldsW now exists(obj obj_is_type(obj lettuce))} = yes
    {HoldsW now obj_is_type(lettuce(1) lettuce)} = yes
    {HoldsW now used(lettuce(1))} = no
    {HoldsW now used(carrot(1))} = no
    {HoldsW now used(egg(1))} = unknown
    {HoldsW now all(obj impl(obj_is_type(obj egg) used(obj)))} = unknown
    {HoldsW now all(obj impl(obj_is_type(obj tomato) used(obj)))} = no
    {HoldsW now exists(obj and(obj_is_type(obj tomato) used(obj)))} = no
    {HoldsW now exists(obj obj_is_type(obj egg))} = yes
    {HoldsW now exists(obj and(obj_is_type(obj egg) neg(used(obj))))} = unknown
    {HoldsW now neg(used(egg(1)))} = unknown
    {HoldsW now and(neg(used(egg(1))) and(neg(used(egg(2))) neg(used(egg(3)))))} = unknown
    {Holds now neg(used(egg(1)))}
    {HoldsW now has_object(joe lettuce(1))} = no
    {HoldsW now exists(a has_object(a lettuce(1)))} = no
    {HoldsW now poss(acquire(joe lettuce(1)))} = yes
    {List.length {Search.base.all proc {$ Q} {Holds now neg(used(_))} Q=unit end}} = 28
    {List.length {Search.base.all proc {$ Q} {Holds now poss(acquire(joe Q))} end}} = 28
    {List.length {Search.base.all proc {$ Q} {Holds now poss(acquire(_ _))} Q=unit end}} = 28*3
    {HoldsW now has_object(jon knife(1))} = no
    {HoldsW now poss(acquire(jon knife(1)))} = yes
    {HoldsW ex(step(action: acquire(jon knife(1)) obs:nil) now) has_object(jon knife(1))} = yes
    {HoldsW ex(step(action: acquire(jon knife(1)) obs:nil) now) poss(acquire(joe knife(1)))} = no
    {HoldsW now poss(chop(jon carrot(1)))} = no
    {HoldsW ex(step(action: acquire(jon knife(1)) obs:nil) now) poss(chop(jon carrot(1)))} = no
    {HoldsW ex(step(action:acquire(jon carrot(1)) obs:nil) ex(step(action: acquire(jon knife(1)) obs:nil) now)) poss(chop(jon carrot(1)))} = yes
    {HoldsW now true} = yes
    {HoldsW now false} = no
    {HoldsW now neg(true)} = no
    {HoldsW ex(step(action:acquire(joe lettuce(1)) obs:nil) now) true} = yes
    {HoldsW ex(step(action:acquire(joe lettuce(1)) obs:nil) now) false} = no

    {HoldsW now poss(acquire(jon carrot(1)))} = yes
    {HoldsW ex(step(action:acquire(joe lettuce(1)) obs:nil) now) poss(acquire(jon carrot(1)))} = yes
    {HoldsW now poss(acquire(jon tomato(1)))} = unknown
    {HoldsW now used(tomato(1))} = unknown
    {HoldsW now neg(used(tomato(1)))} = unknown
    {HoldsW now used(tomato(2))} = unknown
    {HoldsW now neg(used(tomato(2)))} = unknown
    {HoldsW now exists(obj and(obj_is_type(obj tomato) neg(used(obj))))} = unknown
    {HoldsW now exists(obj and(obj_is_type(obj lettuce) used(obj)))} = no
    {HoldsW now all(obj used(obj))} = no
    {HoldsW now all(obj neg(used(obj)))} = unknown
    {HoldsW now all(obj impl(obj_is_type(obj tomato) neg(used(obj))))} = yes
  end

  proc {ShowRun R}
    case R of ex(S R2) then
      {ShowRun R2}
      {System.printInfo " "}
      {System.print S.action}
    else skip end
  end

end
