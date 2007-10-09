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

  Module

export

  Actor
  Actors
  Agents
  Uniformize
  Regress
  ActionOutcomes
  Outcomes
  NewAgentMap

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
           % TODO: assign values to free variables
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

  proc {Outcomes R S Outs}
   skip
  end

  proc {OutcomesA R S Agt Outs}
    CanObs = {HoldsW R canObs(Agt S.action)}
  in
    if CanObs == no then
      Outs = [S]
    else
      Acc = {LP.listAcc Outs}
      CanSense = {HoldsW R canSense(Agt Act)}
     in
      if CanObs == unknown then
        {Acc E}
      end
      if CanSense \= yes then
        {Acc {Step.addobs S o(Agt: [Act])}}
      end
      if CanSense \= no then
        AOuts = {ActionOutcomes Act} in
        if AOuts == nil then
          {Acc {Step.addobs S o(Agt: [Act])}}
        else
         for Res#Cond in AOuts do
            _={LP.ifNot proc {$ _}
                           {Holds R neg(Cond)}
                        end
                        proc {$ _}
                           {Acc {Step.addobs S o(Agt: [Act#Res])}}
                        end}
          end
        end
      end
      {Acc nil}
    end
  end


  end

  Axioms = {FOF.parseRecord {List.toTuple and {DB.query.constraints}} _}
  Initially = {FOF.parseRecord {List.toTuple and {DB.query.initially}} _}

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
      Axioms = {FOF.conj Axioms Initially} in
      {FOF.prove {FOF.impl Axioms Fml} Bind}
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
    Res2
  in
    case R of ex(Step R2) then
      Res2 = {FOF.tautOrCont {FOF.impl Axioms F}}
      if Res2 == taut then Res = yes
      elseif Res2 == cont then Res = no
      else FmlR in
        %TODO: include observations in regression for HoldsW_FOF
        FmlR = {Regress F Step.action}
        {HoldsW_FOF R2 FmlR Res}
      end
    else
      Axioms = {FOF.conj Initially Axioms} in
      Res2 = {FOF.tautOrCont {FOF.impl Axioms F}}
      if Res2 == taut then Res = yes
      elseif Res2 == cont then Res = no
      else Res = unknown end
    end
  end

    
  proc {Test}
    skip
  end

end
