%
%  EQSet.oz:  implements a set of equalities and inequalities.
%

functor

import

  Space
  Combinator

export

  Init
  AddT
  AddF
  Consistent
  Assert

  Test

define

  %
  %  Internally, we simply work with lists of lists of pairs.
  %  It's a conjunction of disjunctions of [in]equalities.
  %

  proc {Init EQ}
    EQ = eqs( t: nil
              f: nil)
  end

  proc {AddT EQIn VIn EQOut}
    if {List.is VIn} then
      EQOut = {Record.adjoinAt EQIn t VIn|EQIn.t}
    else 
      EQOut = {Record.adjoinAt EQIn t [VIn]|EQIn.t}
    end
  end

  proc {AddF EQIn VIn EQOut}
    if {List.is VIn} then
      EQOut = {Record.adjoinAt EQIn f VIn|EQIn.f}
    else 
      EQOut = {Record.adjoinAt EQIn f [VIn]|EQIn.t}
    end
  end

  %
  %  Check an equality set for consistency.  To do so,
  %  simply assert the constraints into a new space and
  %  see what happens.  If it fails, they're inconsistent.
  %
  proc {Consistent EQ B}
    P = proc{$ _} {Assert EQ} end
    S = {Space.new P}
  in
    case {Space.askVerbose S} of failed then B=false
    else B=true
    end
  end

  %
  %  Assert constraints for an equality set into the current space.
  %
  proc {Assert EQ}
    for EList in EQ.t do thread
       {Combinator.'or' {List.toTuple '#' {List.map EList MakeConsT}}}
    end end
    for EList in EQ.f do thread
       {Combinator.'or' {List.toTuple '#' {List.map EList MakeConsF}}}
    end end
  end

  proc {MakeConsT T1#T2 Cons}
    Cons = proc {$} T1 = T2 end
  end

  proc {MakeConsF T1#T2 Cons}
    Cons = proc {$} not T1=T2 end end
  end


  proc {Test}
    E = {Init}
    E1 E2 E3 E4
    V1 V2
  in
    E1 = {AddT E [b#b]}
    {Consistent E1 true}
    E2 = {AddT E1 [c#d]}
    {Consistent E2 false}
    E3 = {AddT {AddT E1 V2#q(f)} V1#p(V2)}
    {IsFree V1 true} {IsFree V2 true}
    {Assert E3}
    V1 = p(q(f))  V2 = q(f)
    E4 = {AddF E3 [V1#p(q(f))]}
    {Consistent E4 false}
  end

end

