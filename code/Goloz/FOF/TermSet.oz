%
%  TermSet.oz:  implements a collection of terms
%
%  Terms are very easily represented as Oz records.
%  We do a little bit of clever(ish) indexing to make searching for a unifying
%  match more efficient - basically hashing on the label and width of the
%  record.
%
%  Since we intend to use this when searching paths in a BDD, we cant use
%  a dictionary and must use an in/out state threading approach.
%
%  The main procedures exported are Put which puts a new term into the
%  set, and Unify.  Unify attempts to unify a given term with a term
%  from the set.  It creates a choicepoint for each such unification
%  that it finds possible, as well as one option where no unification
%  is done.  To determine whether unification was performed or not,
%  it sets a boolean output variable.
%

functor

import

  LP
  Search

export

  Init
  Put
  Unify

  Test

define

  proc {Init TS}
    TS = ts()
  end

  proc {Put Term TSin TSout}
    W = {Record.width Term}
    L = {Record.label Term}
    LMap1 LMapIn LMapOut
    TList
  in
    LMap1 = {Value.condSelect TSin W nil}
    if LMap1 == nil then LMapIn=lm() TList=nil
    else LMapIn=LMap1 TList={Value.condSelect LMapIn L nil} end
    LMapOut = {Record.adjoinAt LMapIn L {Insert Term TList}}
    TSout = {Record.adjoinAt TSin W LMapOut}
  end

  proc {Insert Term In Out}
    if {List.some In proc {$ T B} {LP.termEq T Term B} end} then
       Out = In
    else
       Out = Term|In
    end
  end

  proc {Unify Term TS Res}
    W = {Record.width Term}
    L = {Record.label Term}
    LMap TList
  in
    LMap = {Value.condSelect TS W nil}
    if LMap == nil then Res=false
    else
      TList = {Value.condSelect LMap L nil}
      {Unify_rec Term TList Res}
    end
  end

  proc {Unify_rec Term TList Res}
    case TList of T|Ts then
        % When skiping a potentially unifying term, post a constraint
        % to ensure that it never unifies with that term.
        % This should help eliminate redundant branches in any search.
        dis Term = T Res=true
        []  not Term = T end {Unify_rec Term Ts Res}
        end
    else Res = false
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
    Bindings = {Search.base.all proc {$ S} S=a(_ _) {Unify S TS2 true} end}
    {List.length Bindings 2}
    TS3 = {Put b(x y) TS2}
    Bind2 = {Search.base.all proc {$ S} S=b(_ _)
                               {Unify S TS2 false}
                               {Unify S TS3 true}
                             end}
    Bind2 = [b(x y)]
  end

end

