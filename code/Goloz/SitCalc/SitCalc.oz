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
  Browser

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
  {Module.link ['/storage/uni/pgrad/code/Goloz/FOF/FOF.ozf'] [FOF]}
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
  {Module.link ['/storage/uni/pgrad/code/Goloz/SitCalc/DomainBuilder.ozf' '/storage/uni/pgrad/code/Goloz/Domain.ozf'] [DB Domain]}
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
    elseif {Record.label A1} == check_for then
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
    U = {FOF.parseRecord 'or'(EpsP and(P neg(EpsN))) _}
  end
  Regress = {FOF.transformation 'sitcalc.regress' Regress_atom}

  %
  %  Uniformize the given formula
  %
  proc {Uniformize_atom P U}
    Defn
  in
    Defn = {DB.query.adfluent P}
    if Defn \= nil then U = {Uniformize {FOF.parseRecord Defn _}}
    else Defn in
       Defn = {DB.query.builtin P}
       if Defn \= nil then U = {Uniformize {FOF.parseRecord Defn _}}
       else U = {FOF.parseRecord P _} end
    end
  end
  Uniformize = {FOF.transformation 'sitcalc.uniformize' Uniformize_atom}


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
            {System.show Cond}
            if {HoldsW R Cond} \= no then
               {Acc {Step.setobs S Agt S.action#Res}}
            end
          end
        end
      end
      {Acc nil}
    end
  end

  Axioms = {Uniformize {FOF.parseRecord {List.toTuple and {DB.query.constraints}} _}}
  Initially = {Uniformize {FOF.parseRecord {List.toTuple and {DB.query.initially}} _}}

  %
  %  Determine whether F is known to hold after the run of execution R.
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
  proc {Holds R F}
    Fml Binder Binding
  in
    {FOF.wff F}
    Fml = {FOF.parseRecord F Binder}
    Binding = {HoldsFOF R Fml}
    {Binder Binding}
  end

  proc {HoldsFOF R FmlIn Bind}
    Fml = {Uniformize FmlIn}
  in
    case R of ex(Step R2) then
     if {FOF.contradiction {FOF.impl Axioms Fml}} then
       fail
     else ObsFmls ObsFml FmlR in
       if Step.action \= nil then
         ObsFmls = for collect:C Agt in {Record.arity Step.obs} do
           {C {ObsImplies Agt Step.action Step.obs.Agt}}
         end
         ObsFml = {Uniformize {FOF.parseRecord {List.toTuple and true|ObsFmls} _}}
         FmlR = {Regress {FOF.impl ObsFml Fml} Step.action}
         {HoldsFOF R2 FmlR Bind}
       else
         {HoldsFOF R2 Fml Bind}
       end
     end
    else
      Axs = {FOF.conj Axioms Initially} in
      {FOF.prove {FOF.impl Axs Fml} Bind}
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
  proc {HoldsW R F Res}
    Fml = {FOF.parseRecord F _}
  in
    {System.showInfo "\n\n\n"}
    {FOF.wff F}
    Res = {HoldsW_FOF R Fml}
  end

  proc {HoldsW_FOF R FIn Res}
    F = {Uniformize FIn}
  in
    {System.show holdsw({FOF.toRecord FIn})}
    case R of ex(Step R2) then
      {System.show checking_taut}
      if {FOF.tautology {FOF.impl Axioms F}} then
        Res = yes
      else
        {System.show checking_cont}
        if {FOF.contradiction {FOF.conj Axioms F}} then
          Res = no
        else ObsFmls ObsFml FmlR in
          {System.show regressing}
          if Step.action \= nil then
            ObsFmls = for collect:C Agt in {Record.arity Step.obs} do
              {C {ObsImplies Agt Step.action Step.obs.Agt}}
            end
            ObsFml = {Uniformize {FOF.parseRecord {List.toTuple and true|ObsFmls} _}}
            FmlR = {Regress {FOF.impl ObsFml F} Step.action}
            {HoldsW_FOF R2 FmlR Res}
          else
            {HoldsW_FOF R2 F Res}
          end
        end
      end
    else
      Axs = {FOF.conj Initially Axioms} in
      {System.show checking_taut}
      if {FOF.tautology {FOF.impl Axs F}} then
        Res = yes
      else
        {System.showInfo "\n\n\n\n\n"}
        {System.show checking_cont}
        if {FOF.contradiction {FOF.conj Axs F}} then
          {System.show yep}
          Res = no
        else
          {System.show unknown}
          Res = unknown
        end
      end
    end
  end


  proc {Test}
    F1 F2 F3
  in
    {HoldsW now all(obj impl(obj_is_type(obj tomato) used(obj)))} = unknown
    {HoldsW now exists(obj and(obj_is_type(obj tomato) used(obj)))} = unknown
    raise good_so_far end


    {HoldsW now exists(obj obj_is_type(obj lettuce))} = yes
    {HoldsW now obj_is_type(lettuce(1) lettuce)} = yes
    {HoldsW now used(lettuce(1))} = no
    {HoldsW now used(carrot(1))} = no
    {HoldsW now used(tomato(1))} = unknown
    F1 = {FOF.parseRecord and(all(o nexists(a has_object(a o))) has_object(thomas lettuce(2))) _}
    F2 = {FOF.conj Initially {FOF.parseRecord has_object(thomas lettuce(1)) _}}
    F3 = {FOF.parseRecord and(all(o nexists(a has_object(a o))) exists(a has_object(a lettuce(1)))) _}
    {FOF.contradiction F1 true}
    {FOF.contradiction F2 true}
    {FOF.contradiction F3 true}
    {HoldsW now has_object(thomas lettuce(1))} = no
    {HoldsW now exists(a has_object(a lettuce(1)))} = no
    {HoldsW now poss(acquire(thomas lettuce(1)))} = yes

    {List.length {Search.base.all proc {$ Q} {Holds now neg(used(_))} Q=unit end}} = 29
    {List.length {Search.base.all proc {$ Q} {Holds now poss(acquire(thomas Q))} end}} = 29
    {List.length {Search.base.all proc {$ Q} {Holds now poss(acquire(_ _))} Q=unit end}} = 29*3

    {HoldsW now has_object(harriet knife(1))} = no
    {HoldsW now poss(acquire(harriet knife(1)))} = yes
    {HoldsW ex(step(action: acquire(harriet knife(1)) obs:nil) now) has_object(harriet knife(1))} = yes
    {HoldsW ex(step(action: acquire(harriet knife(1)) obs:nil) now) poss(acquire(thomas knife(1)))} = no

    {HoldsW now poss(chop(harriet carrot(1)))} = no
    {HoldsW ex(step(action: acquire(harriet knife(1)) obs:nil) now) poss(chop(harriet carrot(1)))} = no
    {HoldsW ex(step(action:acquire(harriet carrot(1)) obs:nil) ex(step(action: acquire(harriet knife(1)) obs:nil) now)) poss(chop(harriet carrot(1)))} = yes

    {HoldsW now true} = yes
    {HoldsW now false} = no
    {HoldsW now neg(true)} = no
    {HoldsW ex(step(action:acquire(thomas lettuce(1)) obs:nil) now) true} = yes
    {HoldsW ex(step(action:acquire(thomas lettuce(1)) obs:nil) now) false} = no

    {HoldsW now poss(acquire(harriet carrot(1)))} = yes
    {HoldsW ex(step(action:acquire(thomas lettuce(1)) obs:nil) now) poss(acquire(harriet carrot(1)))} = yes
    {HoldsW now poss(acquire(harriet tomato(1)))} = unknown
    {HoldsW now used(tomato(1))} = unknown
    {HoldsW now neg(used(tomato(1)))} = unknown
    {HoldsW now used(tomato(2))} = unknown
    {HoldsW now neg(used(tomato(2)))} = unknown
    {HoldsW now exists(obj and(obj_is_type(obj tomato) neg(used(obj))))} = unknown
    {HoldsW now exists(obj and(obj_is_type(obj lettuce) used(obj)))} = no
    {HoldsW now all(obj used(obj))} = no
    {HoldsW now all(obj neg(used(obj)))} = unknown
    {HoldsW now all(obj impl(obj_is_type(obj tomato) neg(used(obj))))} = yes
    {HoldsW ex(step(action:check_for(thomas tomato) obs:agtmap(thomas: check_for(thomas tomato)#no)) now) poss(acquire(harriet tomato(1)))} = unknown
    {HoldsW ex(step(action:check_for(thomas tomato) obs:agtmap(thomas: check_for(thomas tomato)#yes)) now) poss(acquire(harriet tomato(1)))} = yes
    
  end

  proc {ShowRun R}
    case R of ex(S R2) then
      {ShowRun R2}
      {System.printInfo " "}
      {System.print S.action}
    else skip end
  end

end
