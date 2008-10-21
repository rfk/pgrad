%
%  LP.oz:  basic logic-programming facilities
%
%  This functor provides some standard logic-programming facilities
%  found in Prolog but missing in Oz.
%

functor 
import

  FD
  Search
  Space
  System

export

  Neg
  IfNot
  Yield
  YieldUniq
  YieldOrdered
  Member
  Union
  Subset
  ListAcc
  SubInTerm
  TermEq
  TermDiff
  TermDiffP
  UnDup
  Touch
  Serialize
  Unserialize
  CopyTerm

define


  % 
  % Standard negation-as-failure on a procedure.
  % Note that the procedure must not wait on free variables, or
  % the search will suspend waiting for them to be bound.
  %
  proc {Neg P}
    {Search.base.one proc {$ L} {P} L=unit end $} = nil
  end

  %
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

  %
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

  %
  %  Yield unique solutions found by the given Search.object, making
  %  choicepoints for each.  Results are passed through function F
  %  before being returned, to canonicalize them.
  %
  proc {YieldUniq Searcher F Res}
    {YieldUniqRec Searcher F nil Res}
  end

  proc {YieldUniqRec Searcher F Found Res}
    Soln = {Searcher next($)}
  in
    case Soln of stopped then fail
    []  nil then fail
    []  [ResT] then Res1={F ResT} in
            if {List.member Res1 Found} then
              {YieldUniqRec Searcher F Found Res}
            else
              choice Res = Res1
              [] {YieldUniqRec Searcher F Res1|Found Res}
              end
            end
    end
  end

  %
  %  Yield solutions from the given search object, ordered according
  %  to the given function {Better Sol1 Sol2}.
  %
  proc {YieldOrdered Searcher Better Res}
    {YieldOrderedRec Searcher Better 0 nil Res}
  end

  proc {YieldOrderedRec Searcher Better Count Sols Res}
    Soln = {Searcher next($)}
  in
    case Soln of stopped then {Member Res Sols}
    []  nil then {Member Res Sols}
    []  [Res1] then Sols2 = {InsertInOrder Res1 Better Sols} in
                    {YieldOrderedRec Searcher Better Count+1 Sols2 Res}
    end
  end

  proc {InsertInOrder I Ord LIn LOut}
    case LIn of H|T then
      if {Ord I H} then LOut = I|LIn
      else LOut = H|{InsertInOrder I Ord T} end
    else LOut = [I] end
  end

  %
  % Backtracking list-membership checking, allowing the members
  % to be enumerated.
  % 
  proc {Member Elem List}
    choice  List = Elem|_
    []      NewL in List=_|NewL {Member Elem NewL}
    end
  end

  %
  % Construct the union of two lists, treating them as sets.
  % Leaves no choicepoints, so it assumes that L1 and L2 are
  % fully bound.
  % 
  proc {Union L1 L2 LF}
    case L1 of nil then LF = L2
    []  H|T then local LI in 
          LI = {Union T L2}
          if {List.member H LI} then
            LF = LI
          else
            LF = H|LI
          end
        end
    end
  end

  %
  %  Determine if one list of a subset of another.
  %
  proc {Subset L1 L2 B}
    case L1 of E|Es then
      if {List.member E L2} then
        B = {Subset Es L2}
      else B = false end
    else B = true end
  end

  %
  %  Incrementally build a list without heaps of ugly temporary vars.
  %  This procedure returns a list and an accumulator function.  Each
  %  call to the accumulator function pushes a value onto the end of
  %  the list.
  %
  proc {ListAcc Lst Acc}
    Tail = {Cell.new Lst}
  in
    proc {Acc V} NewTail in
      case V of nil then @Tail=nil
      else {Cell.exchange Tail V|NewTail NewTail} end
    end
  end

  %
  % Substitute VNew for all occurances of VOld in the given term.
  %
  proc {SubInTerm VOld VNew TIn TOut}
    if {IsFree TIn} then
      TIn = TOut
    else
      if TIn == VOld then
        TOut = VNew
      else
        if {IsRecord TIn} then
          {SubInTerm_Record VOld VNew TIn TOut}
        else
          TIn = TOut
        end
      end
    end
  end

  proc {SubInTerm_Record VOld VNew RIn ROut}
    Fields = {Arity RIn}
  in
    {Record.clone RIn ROut}
    {ForAll Fields proc {$ F}
                     {SubInTerm VOld VNew RIn.F ROut.F}
                   end}
  end


  %
  %  Check for structural equality between terms without blocking.
  %  This is similar to the == predicate in prolog i.e. it treats
  %  different variables as unequal.
  %
  proc {TermEq T1 T2 B}
    TestProc = proc {$ _}  if (T1 == T2) then skip else fail end end
    TestSpace = {Space.new TestProc}
  in
    case {Space.askVerbose TestSpace} of failed then B=false
    []   suspended(_) then B=false
    []   succeeded(_) then B=true
    else raise termEqFailed end
    end
  end

  %
  %  List the differences between two terms.
  %  The output is a list of pairs D1#D2 where D1 is a term within
  %  Term1, and D2 is a *different* term from the same location within
  %  Term2.  If the output list is empty, the terms are identical.
  %
  %  In the extended version {TermDiffP}, Atomic is a
  %  predicate that determines whether a given term should
  %  be treated as atomic i.e. not descended into.
  %
  proc {TermDiff Term1 Term2 Diffs}
    Atomic = proc {$ T B}
      {IsFree T B}
    end
  in
    {TermDiffP Term1 Term2 Atomic Diffs}
  end

  proc {TermDiffP Term1 Term2 Atomic Diffs}
    if {Atomic Term1} orelse {Atomic Term2} then
      if {TermEq Term1 Term2} then
        Diffs = nil
      else
        Diffs = [Term1#Term2]
      end
    else
      if {Record.label Term1} == {Record.label Term2} andthen
      {Record.width Term1} == {Record.width Term2} then DiffList in
          {List.zip {Record.toList Term1} {Record.toList Term2}
                    proc {$ T1 T2 R} {TermDiffP T1 T2 Atomic R} end DiffList}
          Diffs = {List.flatten DiffList}
      else
        Diffs = [Term1#Term2]
      end
    end
  end

  %
  %  Remove duplicate entries from a list
  %
  proc {UnDup LIn LOut}
    {UnDupRec LIn nil LOut}
  end
  proc {UnDupRec LIn SoFar LOut}
    case LIn of L|Ls then
      if {List.member L SoFar} then {UnDupRec Ls SoFar LOut}
      else {UnDupRec Ls L|SoFar LOut} end
    else LOut = SoFar end
  end

  %
  %  Force evaluation of lazy data structures by touching each feature.
  %
  proc {Touch R}
    if {Record.is R} then
      _ = {Record.label R}
      for F in {Record.arity R} do
        {Touch R.F}
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
  %  records from which they can be re-created.
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

