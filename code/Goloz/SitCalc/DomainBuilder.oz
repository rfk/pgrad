%
%  DomainBuilder.oz:  build a domain spec in a relatively declarative fashion
%
%  This functor allows one to build up a domain description in a declarative
%  style (similar to prolog) rather than by defining Oz procedures.  It
%  supports a 'typed' object domain.
%  
%

functor

import

  MSet at '../Utils/MSet.ozf'
  MList at '../Utils/MList.ozf'
  LP at '../Utils/LP.ozf'

  Search
  System
  Combinator
  RecordC

export

  Def
  Query

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

      contains: proc {$ TD Term B}
                  Lbl = {Record.label Term}
                  Res = {Dictionary.condGet TD Lbl unit}
                in
                  if Res == unit then B = false
                  else
                    Args = {Record.toList Term} in
                    {List.length Args} = {List.length Res}
                    B = true
                  end
                end

      constrain: proc {$ TD Term}
                   {ConstrainToList Term {TermDef.templates TD}}
                 end

      templates: proc {$ TD Terms}
                   Terms = for collect:C Lbl#Args in {Dictionary.entries TD} do
                     TermMaker in
                     TermMaker = proc {$ Term}
                     Term = Lbl(...)
                     {RecordC.width Term {List.length Args}}
                     for I#A in {List.mapInd Args fun {$ I A} I#A end} do
                       Arg in
                       Term^I = Arg
                       {Constrain Arg A}
                      end end
                      {C TermMaker}
                   end
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
                 % TODO: should this test whether it's a var term? e.g. v_e()
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
              outcomes: {Dictionary.new}
              conflicts: {MList.new}
              initially: {MList.new}
              constraints: {MList.new}
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
                % Automatically insert action as last argument
                Args = {List.append {Record.toList ADFluent} [action]}
                ADF = {List.toTuple {Record.label ADFluent} Args}
              in
                {TermDef.insert Data.adfluents ADF}
              end

    conflicts: proc {$ Proc}
                 {MList.cons Data.conflicts Proc}
               end

    initially: proc {$ Fml}
                 {MList.cons Data.initially Fml}
               end

    constraint: proc {$ Fml}
                 {MList.cons Data.constraints Fml}
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

    outcome: proc {$ Action Outcome Func}
               OldV NewV Lst Def
             in
               {Dictionary.condExchange Data.outcomes Action nil OldV NewV}
               if OldV == nil then Lst = {MList.new} Def = unit
               else Lst#Def = OldV end
               if Func == default then
                   NewV = Lst#Outcome
               else
                   NewV = Lst#Def
                   {MList.cons Lst Outcome#Func}
               end
             end

  )


  proc {GetSubTypes Super Subs}
    if Super == object then
      Subs = for collect:C T in {Dictionary.keys Data.objects} do
               {C T}
             end
    else
      Subs = {Search.base.all proc {$ T} {IsSubType Super T} end}
    end
  end
  proc {IsSubType Super Sub}
    choice Super = Sub
    []  {IsSubTypeP Super Sub}
    []  Sub2 in {IsSubTypeP Super Sub2} {IsSubType Sub2 Sub}
    end
  end
  proc {IsSubTypeP Super Sub}
    {IsSubTypePRec {MList.toList Data.superTypes} Super Sub}
  end
  proc {IsSubTypePRec Lst Super Sub}
    case Lst of Sp#Sb|T then
      choice Super=Sp Sub=Sb
      []  {IsSubTypePRec T Super Sub}
      end
    else fail end
  end

  proc {Constrain A R}
    if R == agent then
      {ConstrainToList A {MSet.toList Data.agents}}
    elseif R == action then
      {TermDef.constrain Data.actions A}
    elseif R == type then
      {ConstrainToList A object|{GetSubTypes object}}
    else 
      {ConstrainToList A {Query.objs_of_type R}}
    end
  end

  proc {ConstrainToList V Lst}
    Cons = {List.map Lst fun {$ I}
             if {Procedure.is I} then
               proc {$} V = {I} end
             else
               proc {$} V = I end
             end
           end}
  in
    thread {Combinator.'or' {List.toTuple '#' Cons}} end
  end
  

  %
  %  Procedures for querying the domain data
  %
  Query = q(

      assign:  proc {$ V}
                 choice {LP.member V {MSet.toList Data.agents}}
                 [] Y = for return:R default:false
                        T in {Dictionary.keys Data.objects} do
                          choice
                            M = {Dictionary.get Data.objects T}
                            Ns = for collect:C I in 1..M do {C I} end N in
                            {LP.member N Ns}  V = T(N)  {R true}
                          [] skip end
                        end in
                    if Y then skip else fail end
                 end
               end

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

      initially: proc {$ Fmls}
                   Fmls = {MList.toList Data.initially}
                 end

      constraints: proc {$ Fmls}
                   Fmls = {MList.toList Data.constraints}
                 end

      adfluent: proc {$ Fluent Defn}
                  Lbl = {Record.label Fluent}
                  ArgsT = {Record.toList Fluent}
                  Act Args
                in
                  {List.takeDrop ArgsT {List.length ArgsT}-1 Args [Act]}
                  if {TermDef.contains Data.adfluents Fluent} == false then
                    Defn = nil
                  else
                    {TermActFml.query Data.adfDefs {List.toTuple Lbl Args} Act Defn}
                  end
                end

      objs_of_type: proc {$ Type Objs}
                      Objs = for collect:C SType in {GetSubTypes Type} do
                               Nm = {Dictionary.condGet Data.objects SType nil}
                             in
                               if Nm \= nil then
                                 for X in 1..Nm do
                                   {C SType(X)}
                                 end
                               end
                             end
                    end

      wfp: proc {$ P}
             if {TermDef.contains Data.adfluents P} then
               {TermDef.constrain Data.adfluents P}
             elseif {TermDef.contains Data.fluents P} then
               {TermDef.constrain Data.fluents P}
             elseif {Query.builtin P} \= nil then
               skip
             else fail end
           end

      builtin: proc {$ Fluent Defn}
                 case Fluent of obj_is_type(Obj Type) then Disjs in
                   Disjs = for collect:C ObjT in {Query.objs_of_type Type} do
                             {C eq(Obj ObjT)}
                           end
                   Defn = {List.toTuple 'or' Disjs}
                 else Defn = nil end
               end

      outcomes: proc {$ Action Outcomes}
                  Lbl = {Record.label Action}
                  Args = {Record.toList Action}
                  OutDefs = {Dictionary.condGet Data.outcomes Lbl nil#unit}
                  Lst OutT Conds
                in
                  if OutDefs.1 == nil then Lst = nil
                  else Lst = {MList.toList OutDefs.1} end
                  if Lst == nil andthen OutDefs.2 == unit then
                    Outcomes = [ok#true]
                  else
                    OutT = for collect:C O#F in Lst do
                             {C O#{F Args}}
                           end
                    Conds = for collect:C _#F in Lst do
                             {C neg({F Args})}
                            end
                    Outcomes = (OutDefs.2#{List.toTuple and true|Conds})|OutT
                  end
                end

  )


end
