%
%  LP.oz:  basic logic-programming facilities
%
%  This functor provides some standard logic-programming facilities
%  found in e.g. Prolog but missing in Oz.
%

functor 
import

  Search
  Space

export

  Neg
  IfNot
  Yield
  Member
  Union
  ListAcc
  SubInTerm
  TermEq
  TermDiff
  TermDiffP
  UnDup

  Test

define


  %
  % Assert that a predicate has at least one solution.
  % This procedure searches for a single solution to a predicate,
  % and 
  %

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

  proc {UnDup LIn LOut}
    {UnDupRec LIn nil LOut}
  end
  proc {UnDupRec LIn SoFar LOut}
    case LIn of L|Ls then
      if {List.member L SoFar} then {UnDupRec Ls SoFar LOut}
      else {UnDupRec Ls L|SoFar LOut} end
    else LOut = SoFar end
  end


  proc {Test}
    V1 V2 Lst Acc
  in
    {TermEq a a true}
    {TermEq a b false}
    {TermEq t(V1 V2) t(V1 V2) true}
    {TermEq t(V1 V2) t(V1 V1) false}
    {TermEq t(V1 V2) t(b V2) false}
    {TermEq V1 V1 true}
    {TermEq V2 V1 false}
    {ListAcc Lst Acc}
    {IsFree Lst true}
    {Acc 1}
    Lst = 1|_
    {Acc 2}
    Lst = 1|2|_
    {Acc nil}
    Lst = [1 2]
  end

end

