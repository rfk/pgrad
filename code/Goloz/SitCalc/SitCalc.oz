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
           %for V in Vs do
           %  {DB.query.assign V}
           %end
           skip
         end
  )

  %
  %  Make a private DomainBuilder, and import definitions from Domain.oz
  %  We'll pass all domain-dependant queries to DB.query
  %
  DB = _
  Domain = _
  {Module.link ['SitCalc/DomainBuilder.ozf' 'Domain.ozf'] [DB Domain]}
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
    B = ({Record.label A1} \= {Record.label A2})
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
    if Defn \= nil then U = {FOF.parseRecord Defn _}
    else Defn in
       Defn = {DB.query.builtin P}
       if Defn \= nil then U = {FOF.parseRecord Defn _}
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
            if {HoldsW R neg(Cond)} \= no then
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
     else FmlR in
       %TODO: include observations in regression for holdsFOF
       FmlR = {Regress Fml Step.action}
       {HoldsFOF R2 FmlR Bind}
     end
    else
      Axs = {FOF.conj Axioms Initially} in
      {FOF.prove {FOF.impl Axs Fml} Bind}
    end
  end

  %
  %  Determine if it is known whether F holds after the run of execution R.
  %  Unlike {Holds}, this procedure returns one of 'yes', 'no' or
  %  'unknown' and will not bind free variables.
  %
  proc {HoldsW R F Res}
    Fml = {FOF.parseRecord F _}
  in
    Res = {HoldsW_FOF R Fml}
  end

  proc {HoldsW_FOF R FIn Res}
    F = {Uniformize FIn}
  in
    case R of ex(Step R2) then
      if {FOF.tautology {FOF.impl Axioms F}} then Res = yes
      elseif {FOF.contradiction {FOF.conj Axioms F}} then Res = no
      else FmlR in
        %TODO: include observations in regression for HoldsW_FOF
        FmlR = {Regress F Step.action}
        {HoldsW_FOF R2 FmlR Res}
      end
    else
      Axs = {FOF.conj Initially Axioms} in
      if {FOF.tautology {FOF.impl Axs F}} then Res = yes
      elseif {FOF.contradiction {FOF.conj Axs F}} then Res = no
      else Res = unknown end
    end
  end


  proc {Test}
    F1 F2 
  in
    {HoldsW now exists(obj obj_is_type(obj lettuce))} = yes
    {HoldsW now obj_is_type(lettuce(1) lettuce)} = yes
    {HoldsW now used(lettuce(1))} = no
    {HoldsW now used(tomato(1))} = unknown
    F1 = {FOF.parseRecord and(all(o nexists(a p(a o))) p(agt obj)) _}
    F2 = {FOF.conj Initially {FOF.parseRecord has_object(thomas lettuce(1)) _}}
    {FOF.contradiction F1 true}
    {FOF.contradiction F2 true}
    {HoldsW now has_object(thomas lettuce(1))} = no
    {HoldsW now exists(a has_object(a lettuce(1)))} = no
    {HoldsW now poss(acquire(thomas lettuce(1)))} = yes

    {List.length {Search.base.all proc {$ Q} {Holds now neg(used(lettuce(1)))} Q=unit end}} = 1
  end

end
