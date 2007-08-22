%
%  LP.oz:  basic logic-programming facilities
%
%  This functor provides some standard logic-programming facilities
%  found in e.g. Prolog but missing in Oz.
%

functor 
import

  Search
  Browser

export

  neg: Neg
  ifNot: IfNot
  member: Member
  union: Union
  subInTerm: SubInTerm

define

  % 
  % Standard negation-as-failure on a procedure
  %
  % TODO: need to ensure that the procedure has no free variables,
  %       or the search will hang waiting for them to be bound.
  %
  proc {Neg P}
    {Search.base.one proc {$ L} {P} L=unit end $} = nil
  end

  %
  % Execute Proc2 if Proc1 has no solutions.
  % This is useful to avoid unnecesary re-computiation of Proc1, as would
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
                    [] {YieldAll Searcher Res}
                    end
    end
  end

  proc {YieldAll Searcher Res}
    Soln
  in
    {Searcher next(Soln)}
    case Soln of stopped then fail
    []  nil then fail
    []  [Res1] then choice Res = Res1
                    [] {YieldAll Searcher Res}
                    end
    end
  end

  %
  % Backtracking list-membership checking, allowing the members
  % to be enumerated.
  % 
  proc {Member Elem List}
    dis  List = Elem|_
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

end

