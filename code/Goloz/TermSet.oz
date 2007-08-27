%
%  TermSet.oz:  implements a collection of terms (Oz records)
%
%  We do a little bit of clever(ish) indexing to make searching for a unifying
%  match more efficient - basically hashing on the label and width of the
%  record.
%
%  Since we intend to use this when searching paths in a BDD, we cant use
%  a dictionary and must use an in/out threading  approach.
%
%  The main procedures exported are Put which (clearly) puts a new term
%  into the set, and Unify, which will attempt to unify a given term
%  with an entry in the set.  It creates a choicepoint for each possible
%  unification, or fails if no unification is possible.  This operation can
%  bind variables within the set (and in fact this is usually its intention).
%
%  We also provide the procedure NoUnify, which posts constraints stating
%  that a term must never become unified with anything in the set. This
%  could be useful in pruning a search space, for example.
%

functor

import

  Search

export

  Init
  Put
  Unify
  NoUnify

  Test

define

  proc {Init TS}
    TS = unit()
  end

  proc {Put Term TSin TSout}
    W = {Record.width Term}
    L = {Record.label Term}
    LMap1 LMapIn LMapOut
    TList
  in
    LMap1 = {Value.condSelect TSin W nil}
    if LMap1 == nil then LMapIn=unit() TList=nil
    else LMapIn=LMap1 TList={Value.condSelect LMapIn L nil} end
    LMapOut = {Record.adjoinAt LMapIn L Term|TList}
    TSout = {Record.adjoinAt TSin W LMapOut}
  end

  proc {Unify Term TS}
    W = {Record.width Term}
    L = {Record.label Term}
    LMap TList
  in
    LMap = {Value.condSelect TS W nil}
    if LMap == nil then fail end
    TList = {Value.condSelect LMap L nil}
    {Unify_rec Term TList}
  end

  proc {Unify_rec Term TList}
    case TList of T|Ts then
        dis Term = T
        []  {Unify_rec Term Ts}
        end
    else fail
    end
  end

  proc {NoUnify Term TS}
    W = {Record.width Term}
    L = {Record.label Term}
    LMap TList
  in
    LMap = {Value.condSelect TS W nil}
    if LMap \= nil then
      TList = {Value.condSelect LMap L nil}
      {NoUnify_rec Term TList}
    end
  end

  proc {NoUnify_rec Term TList}
    case TList of T|Ts then
        not Term = T end
        {NoUnify_rec Term Ts}
    else skip
    end
  end


  proc {Test}
    TS = {Init}
    TS1 TS2 TS3
    Bindings Bind2
  in
    {Record.width TS 0}
    {Put a(1 2) TS TS1}
    {Record.width TS1 1}
    TS1.2.a = [a(1 2)]
    {Put a(2 3) {Put b(c d) TS1} TS2}
    {List.length TS2.2.a 2}
    {List.length TS2.2.b 1}
    Bindings = {Search.base.all proc {$ S} S=a(_ _) {Unify S TS2} end}
    {List.length Bindings 2}
    TS3 = {Put b(x y) TS2}
    Bind2 = {Search.base.all proc {$ S} S=b(_ _) {NoUnify S TS2} {Unify S TS3} end}
    Bind2 = [b(x y)]
  end

end

