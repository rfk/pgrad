%
%  DomainBuilder.oz:  build a domain spec in a relatively declarative fashion
%
%  This functor allows one to build up a domain description in a declarative
%  style (similar to prolog) rather than by defining Oz procedures.  It
%  supports a 'typed' object domain.
%  
%
%

functor

import

  LP
  MSet at '../Mutable/Set.ozf'
  MList at '../Mutable/List.ozf'

export

  Def
  Query
  Data %TODO: don't export Data from this module

define

  %
  %  Manages a collection of term definitions.
  %
  TermDef = td(
      new: proc {$ TD}
             TD = {Dictionary.new}
           end

      insert: proc {$ TD Term}
                Lbl = {Record.label Term}
                Args = {Record.toList Term}
              in
                {Dictionary.put TD Lbl Args}
              end

      inst: proc {$ TD Label Term}
              Args = {Dictionary.get TD Label}
            in
              Term = {List.toTuple Label {List.makeList {List.length Args}}}
            end
  )


  %
  %  Manages a collection of term/action formulae.  These are functions
  %  that return a formula describing a relationship between two
  %  terms.  For example, the formula indicating when fluent(...) is
  %  made true by action(...).
  %
  TermActFml = tpf(
      new: proc {$ TP}
             TP = {Dictionary.new}
           end
 
      insert: proc {$ TP Label1 Label2 Func}
                OldV ActMap
              in
                {Dictionary.condExchange TP Label1 nil OldV ActMap}
                if OldV == nil then ActMap = {Dictionary.new}
                else ActMap = OldV end
                {Dictionary.put ActMap Label2 Func}
              end

      query: proc {$ TP Term Act Fml}
               Label1 = {Record.label Term}
               Args1 = {Record.toList Term}
               ActMap
             in
               ActMap = {Dictionary.condGet TP Label1 nil}
               if ActMap == nil then Fml = false
               else
                 % TODO: should this test whether it's a var term e.g. v_e()
                 if {IsFree Act} then Fmls in
                   % Enumerate each possible action and disjoin the results
                   Fmls = for collect:C ActNM in {Dictionary.keys ActMap} do
                     Act2 = {TermDef.inst Data.actions ActNM}
                     Fml2 = {TermActFml.query TP Term Act2} in
                     {C {ApplyExQuants {Record.toList Act2} Fml2}}
                   end
                   if Fmls == nil then Fml = false
                   else Fml = {List.toTuple 'or' Fmls} end
                 else Func
                   Label2 = {Record.label Act}
                   Args2 = {Record.toList Act} in
                   Func = {Dictionary.condGet ActMap Label2 nil}
                   if Func == nil then Fml = false
                   else Fml = {Func Args1 Args2} end
                 end
               end
             end
  )

  proc {ApplyExQuants Vars FmlAcc Fml}
    case Vars of V|Vs then
      {ApplyExQuants Vs exists(V FmlAcc) Fml}
    else Fml = FmlAcc end
  end
  
  %
  %  Private record holding the domain data
  %
  Data = data(agents: {MSet.new}
              superTypes: {MList.new} 
              objects: {Dictionary.new}
              actions: {TermDef.new}
              fluents: {TermDef.new}
              adfluents: {TermDef.new}
              adfDefs: {TermActFml.new}
              causesTrue: {TermActFml.new}
              causesFalse: {TermActFml.new}
              conflicts: {MList.new}
             )

  %
  %  Procedures for declaring the domain data.
  %
  Def = d(

    agent: proc {$ A}
             {MSet.insert Data.agents A}
           end

    object: proc {$ Type Num}
             {Dictionary.put Data.objects Type Num}
            end

    superType: proc {$ Super Sub}
                 {MList.cons Data.superTypes (Super#Sub)}
               end

    action: proc {$ Action}
              {TermDef.insert Data.actions Action}
            end

    fluent: proc {$ Fluent}
              {TermDef.insert Data.fluents Fluent}
            end

    adfluent: proc {$ ADFluent}
                {TermDef.insert Data.adfluents ADFluent}
              end

    conflicts: proc {$ Proc}
                 {MList.cons Data.conflicts Proc}
               end

    adfDef: proc {$ Fluent Action Func}
              {TermActFml.insert Data.adfDefs Fluent Action Func}
            end

    causesTrue: proc {$ Fluent Action Func}
                  {TermActFml.insert Data.causesTrue Fluent Action Func}
                end

    causesFalse: proc {$ Fluent Action Func}
                   {TermActFml.insert Data.causesFalse Fluent Action Func}
                 end

  )


  %
  %  Procedures for querying the domain data
  %
  Query = q(

      agent:  proc {$ A}
                {MSet.member Data.agents A}
              end

      agents: proc {$ Agts}
                Agts = {MSet.toList Data.agents}
              end

      causesTrue: proc {$ Fluent Action Fml}
                    {TermActFml.query Data.causesTrue Fluent Action Fml}
                  end

      causesFalse: proc {$ Fluent Action Fml}
                     {TermActFml.query Data.causesFalse Fluent Action Fml}
                   end

  )


end
