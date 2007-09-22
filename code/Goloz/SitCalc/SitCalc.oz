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
  Execution

  Module

export

  Actor
  Actors
  Agents
  Uniformize
  Regress
  fof: FOF
  ActionOutcomes
  NewAgentMap
  Axioms
  Initially

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


  proc {NewAgentMap M}
    Names = {DB.query.agents} in
    M = {Record.adjoinList agtmap {List.map Names fun {$ E} E#_ end}}
  end

  proc {ActionOutcomes Act Outcomes}
    Outcomes = {DB.query.outcomes Act}
  end 

  Axioms = {FOF.parseRecord {List.toTuple and {DB.query.constraints}} _}
  Initially = {FOF.parseRecord {List.toTuple and {DB.query.initially}} _}
    
  Jplan = jplan(

    init: proc {$ JP}
            JP = {NewAgentMap}
          end

    finish: proc {$ JP}
              skip
              %for CP in {Record.toList JP} do
              %  CP = nil
              %end
            end

    extend: proc {$ JP E Branches}
              Outcomes = {Execution.outcomes E}
              JPStep = JP %{Jplan.addstep JP E}
            in
              {Jplan.extendRec JPStep Outcomes Branches}
            end

    extendRec: proc {$ JPBase Outcomes Branches}
                 case Outcomes of E|Es then B2 JPt={NewAgentMap} in
                   %for Agt in {Record.arity JPBase} do
                   %  if E.1.obs.Agt == nil then
                   %  else
                   %    {Jplan.ensureObs JPBase.Agt E.1.obs.Agt JPt.Agt}
                   %  end
                   %end
                   Branches = E#JPt|B2
                   {Jplan.extendRec JPBase Es B2}
                 else
                   %for Agt in {Record.arity JPBase} do
                   %  {Jplan.finishObs JPBase.Agt}
                   %end
                   Branches = nil
                 end
               end

    ensureObs: proc {$ JPBase Obs JPt}
                 if {IsFree JPBase} then
                   JPBase = obs(Obs JPt _)
                 else JPt2 JPf Obs2 in
                   JPBase = obs(Obs2 JPt2 JPf)
                   if Obs2 == Obs then JPt = JPt2
                   else {Jplan.ensureObs JPf Obs JPt} end
                 end
               end

    finishObs: proc {$ JPBase}
                 if {IsFree JPBase} then JPBase = nil
                 else JPf in JPBase = obs(_ _ JPf) {Jplan.finishObs JPf} end
               end

    addstep: proc {$ JP E JPOut}
               JPOut = {NewAgentMap}
               for Agt in {Record.arity JP} do MyActs in
                 MyActs = for collect:C Act in E.1.action do
                            if {Actor Act} == Agt then
                              {C Act}
                            end
                          end
                 if MyActs == nil then JPOut.Agt = JP.Agt
                 else JP.Agt = seq(E.1.action JPOut.Agt) end
               end
             end

    fromExs: proc {$ Exs JP}
               case Exs of E|Es then
                 {Jplan.fromEx E JP _}
                 {Jplan.fromExs Es JP}
               else 
                 for Agt in {Record.arity JP} do
                   {Jplan.closeoff JP.Agt}
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
    fromEx: proc {$ E JPBase JPHead}
              JPHead = {NewAgentMap}
              case E of ex(Step E2) then
                JPTail = {Jplan.fromEx E2 JPBase}
                JPStep = {NewAgentMap} in
                for Agt in {Record.arity JPTail} do MyActs MyObs in
                  MyActs = for collect:C Actn in Step.action do
                             if {Actor Actn} == Agt then {C Actn} end
                           end
                  % TODO: should we include the entire joint action?
                  % Seems like they should need to know it for coordination
                  if MyActs \= nil then
                    JPTail.Agt = seq(MyActs JPStep.Agt)
                  else
                    JPTail.Agt = JPStep.Agt
                  end
                  MyObs = {Value.condSelect Step.obs Agt nil}
                  if MyObs \= nil then
                    {Jplan.ensureObs JPStep.Agt MyObs JPHead.Agt}
                  else
                    JPHead.Agt = JPStep.Agt
                  end
                end
              else JPHead = JPBase end
            end

    closeoff: proc {$ JP}
                if {IsFree JP} then
                  JP = nil
                else
                  case JP of seq(_ JP2) then {Jplan.closeoff JP2}
                  []   obs(_ JP1 JP2) then
                           {Jplan.closeoff JP1}
                           {Jplan.closeoff JP2}
                  end
                end
              end

  )


  proc {Test}
    skip
  end

end
