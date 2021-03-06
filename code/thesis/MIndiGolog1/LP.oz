%
%  LP.oz:  generic logic-programming procedures
%
%  Copyright 2008, Ryan Kelly
%
%  This file provides some utility procedures to make Prolog-style logic
%  programming in Oz more pleasant.
%

functor 

import

  Search
  System
  FD

export

  Neg
  IfNot
  Yield
  Member
  Union

  SubInTerm
  CopyTerm
  Serialize
  Unserialize
  OMap_get

define

  % Standard negation-as-failure on a nullary procedure
  %
  % Unlike prolog, this cannot close over free variables.  If the
  % input procedure uses free variables, the search will hang waiting
  % for them to be bound.
  %
  % If you need prolog style behavior, you can do it using LP.copyTerm:
  %
  %   local V in
  %     {LP.neg proc {$} 
  %        Vl = {LP.copyTerm V} in
  %        {ProcToNegate Vl}
  %     end}
  %   end
  %
  proc {Neg P}
    {Search.base.one proc {$ L} {P} L=unit end $} = nil
  end

  % Execute Proc2 if Proc1 has no solutions.
  % This is useful to avoid unnecesary re-computation of Proc1, as would
  % be done by the following (equivalent) prolog:
  %
  %   ifnot(P1,P2,Res) :-  P1(Res) ; not(P1(_)), P2(Res)
  %
  % We expect Proc1 and Proc2 to be unary procedures as usual.
  % Results will be bound to the output variable Res.
  %
  proc {IfNot Proc1 Proc2 Res}
    Searcher Soln
  in
    Searcher = {New Search.object script(Proc1)}
    {Searcher next(Soln)}
    case Soln of stopped then fail
    []  nil then {Proc2 Res}
    []  [Res1] then choice Res = Res1
                    [] {Yield Searcher Res}
                    end
    end
  end

  %  Yield the solutions found by the given Search.object, making
  %  choicepoints for each.
  %
  proc {Yield Searcher Res}
    Soln = {Searcher next($)}
  in
    case Soln of stopped then fail
    []  nil then fail
    []  [Res1] then choice Res = Res1
                    [] {Yield Searcher Res}
                    end
    end
  end

  % Nondeterministic selection of list member
  %
  proc {Member Elem List}
    choice  List = Elem|_
    []      NewL in List=_|NewL {Member Elem NewL}
    end
  end

  % Set-union of two lists
  %
  proc {Union L1 L2 LF}
    case L1 of
        nil then LF = L2
    []  H|T then local LI in 
          LI = {Union T L2}
          choice {Member H LI} LF = LI
          [] LF = H|LI
          end
        end
    end
  end


  % Term substitution - replace all occurrences of VOld with VNew
  % in TIn, to produce new term TOut.
  %
  proc {SubInTerm VOld VNew TIn TOut}
    if {IsFree TIn} then
      TIn = TOut
    else
      if TIn == VOld then
        TOut = VNew
      else
        if {IsRecord TIn} then
          TOut = {Record.map TIn proc {$ FIn FOut}
                   FOut = {SubInTerm VOld VNew FIn}
                 end}
        else
          TIn = TOut
        end
      end
    end
  end

  %  Make a copy of the input term, renaming free/kinded variables.
  %
  proc {CopyTerm TIn TOut}
    {CopyTermRec _ TIn TOut}
  end

  proc {CopyTermRec Vars TIn TOut}
    if {IsFree TIn} then
      TOut = {OMap_get Vars TIn _}
    else
      if {IsDet TIn} then
        if {IsRecord TIn} then
          TOut = {Record.map TIn proc {$ FIn FOut}
                   FOut = {CopyTermRec Vars FIn}
                 end}
        else
          % TODO: any other tricky recursive cases?
          TOut = TIn
        end
      else
        if {IsKinded TIn} then Kind in
          TOut = {OMap_get Vars TIn _}
          {Value.status TIn kinded(Kind)}
          % TODO: copy other kinded constraints, e.g. records
          if Kind == int then
              % We assume only linear constraints, so copying min/max is valid
              {FD.decl TOut}
              TOut >=: {FD.reflect.min TIn}
              TOut =<: {FD.reflect.max TIn}
          end
        else
          TOut = TIn
        end
      end
    end
  end
    
  %  Serialize a term, replacing free/kinded variables with specially named
  %  records from which they can be re-created.  This is needed to communicate
  %  partially-instantiated records outside their original computation space.
  %
  %  Note that this is *extremely* bad Oz practise, but it the simplest way
  %  the achieve what we want without moving too far from standard Golog
  %  implementation techniques, which assume prolog-style free variables.
  %
  proc {Serialize TIn TOut}
    {SerializeRec _ TIn TOut}
  end

  proc {SerializeRec Vars TIn TOut}
    if {IsFree TIn} then Nm in
      Nm = {OMap_get Vars TIn {NewGlobalName}}
      TOut = lp_var(Nm)
    else
      if {IsDet TIn} then
        if {IsRecord TIn} then
          TOut = {Record.map TIn proc {$ FIn FOut}
                   FOut = {SerializeRec Vars FIn}
                 end}
        else
          TOut = TIn
        end
      else
        if {IsKinded TIn} then Kind in
          {Value.status TIn kinded(Kind)}
          if Kind == int then Nm in
              % We assume only linear constraints, so copying min/max is valid
              Nm = {OMap_get Vars TIn {NewGlobalName}}
              TOut = lp_fd(Nm {FD.reflect.min TIn} {FD.reflect.max TIn})
          else Nm in
              % TODO: copy other kinded constraints, e.g. records
              Nm = {OMap_get Vars TIn {NewGlobalName}}
              TOut = lp_var(Nm)
          end
        else
          TOut = TIn
        end
      end
    end
  end

  proc {Unserialize TIn TOut}
    {UnserializeRec _ TIn TOut}
  end

  proc {UnserializeRec Vars TIn TOut}
    if {IsDet TIn} then
      if {IsRecord TIn} then
        case TIn of lp_var(Nm) then
                    TOut = {OMap_get Vars Nm _}
        []   lp_fd(Nm Min Max) then
                    TOut = {OMap_get Vars Nm _}
                    {FD.decl TOut}
                    TOut >=: Min
                    TOut =<: Max
        else TOut = {Record.map TIn proc {$ FIn FOut}
                      FOut = {UnserializeRec Vars FIn}
                    end}
        end
      else
        TOut = TIn
      end
    else
      raise lp_unserialize_nondet end
    end
  end

  %  Retrieve the value for Name in the open-ended map Map.
  %  If it does not exist, set it to Default.
  %
  proc {OMap_get Map Name Default Val}
    if {IsFree Map} then
      Map = (Name#Default)|_
      Val = Default
    else Nm1 Val1 Map1 in
      Map = (Nm1#Val1)|Map1
      if {System.eq Name Nm1} then
        Val = Val1
      else
        {OMap_get Map1 Name Default Val}
      end
    end
  end

  %  Allow creation of new unique names from within a subordinated computation
  %  space.  This is pretty similar to prolog's gensym/2 predicate.
  %
  NewGlobalName = _
  local IPort IStream in
    IPort = {Port.new IStream}
    thread
      for unit#Nm in IStream do
        {NewName Nm}
      end
    end
    proc {NewGlobalName Nm}
      Nm = !!{Port.sendRecv IPort unit}
    end
  end
  

end

