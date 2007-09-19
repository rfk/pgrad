%
%  Domain.oz:  specifics of the sitcalc domain under operation
%
%  This file specifies the specific dynamics of the domain being executed
%  in, such as successor-state axioms and possibility axioms.
%

functor 

import

  DomainBuilder at 'SitCalc/DomainBuilder.ozf'
  LP

define

  D = DomainBuilder.def

  {D.agent thomas}
  {D.agent richard}
  {D.agent harriet}

  {D.object knife 2}
  {D.object bowl 3}
  {D.object board 3}
  {D.object oven 1}
  {D.object flour 5}
  {D.object sugar 6}
  {D.object egg 3}
  {D.object tomato 2}
  {D.object lettuce 3}
  {D.object carrot 3}

  {D.superType appliance oven}
  {D.superType container bowl}
  {D.superType container board}
  {D.superType container appliance}
  {D.superType ingredient flour}
  {D.superType ingredient egg}
  {D.superType ingredient tomato}
  {D.superType ingredient lettuce}
  {D.superType ingredient sugar}

  {D.action acquire(agent object)}
  {D.action release(agent object)}
  {D.action place_in(agent object container)}
  {D.action transfer(agent container container)}

  {D.fluent has_object(agent object)}
  {D.fluent used(object)}
  {D.fluent contents(container object)}

  {D.adfluent poss}
  {D.adfluent canObs(agent)}
  {D.adfluent canSense(agent)}

  {D.adfDef poss acquire fun {$ _ [_ Obj]}
        and(all(a neg(has_object(a Obj))) neg(used(Obj)))
  end}
  {D.adfDef poss release fun {$ _ [Agt Obj]}
        has_object(Agt Obj)
  end}
  {D.adfDef poss transfer fun {$ _ [Agt Src Dst]}
        and(has_object(Agt Src) has_object(Agt Dst)
            exists(c contents(Src c)))
  end}
  {D.adfDef poss place_in fun {$ _ [Agt Obj Dst]}
        and(has_object(Agt Obj) has_object(Agt Dst)
            neg(obj_is_type(Obj appliance)))
  end}

  {D.adfDef canObs acquire fun {$ _ _} true end}
  {D.adfDef canObs release fun {$ _ _} true end}
  {D.adfDef canObs transfer fun {$ _ _} true end}
  {D.adfDef canObs place_in fun {$ _ _} true end}

  {D.adfDef canSense acquire fun {$ [Agt] Agt2|_ } eq(Agt Agt2) end}
  {D.adfDef canSense release fun {$ [Agt] Agt2|_ } eq(Agt Agt2) end}
  {D.adfDef canSense transfer fun {$ [Agt] Agt2|_ } eq(Agt Agt2) end}
  {D.adfDef canSense place_in fun {$ [Agt] Agt2|_ } eq(Agt Agt2) end}

  {D.causesTrue has_object acquire fun {$ [Af Of] [Aa Oa]}
      and(eq(Af Aa) eq(Of Oa))
  end}
  {D.causesFalse has_object release fun {$ [Af Of] [Aa Oa]}
      and(eq(Af Aa) eq(Of Oa))
  end}
  {D.causesFalse has_object place_in fun {$ [Af Of] [Aa Oa _]}
      and(eq(Af Aa) eq(Of Oa) obj_is_type(Of ingredient))
  end}

  {D.causesTrue used acquire_object fun {$ [Of] [_ Oa]}
      eq(Of Oa)
  end}

  {D.causesTrue contents place_in fun {$ [ObjF ContsF] [_ ContsA ObjA]}
      and(eq(ObjF ObjA)
      'or'(and(neg(exists(c contents(ObjF c))) eq(ContsF ContsA))
           exists(c and(contents(ObjF c) eq(ContsF add(ContsA c))))))
  end}
  {D.causesTrue contents transfer fun {$ [ObjF ContsF] [_ SrcA DstA]}
      and(eq(ObjF DstA)
      exists(cs and(contents(SrcA cs)
        'or'(and(neg(exists(c contents(ObjF c))) eq(cs ContsF))
             exists(c and(contents(ObjF c) eq(ContsF add(cs c))))))))
  end}

  {D.conflicts proc {$ Act} A1 A2 Obj in
       {LP.member acquire_object(A1 Obj) Act}
       {LP.member acquire_object(A2 Obj) Act}
       (A1 \= A2)=true
  end}

  %{D.outcome acquire success fun {$ _} true end}

  {D.initially all(obj nexists(agt has_object(agt obj)))}
  {D.initially nexists(obj used(obj))}
  {D.initially all(obj nexists(c contents(obj c)))}

  % TODO: this constraint hangs the prover
  %{D.constraint all(agt1 all(agt2 all(obj impl(and(has_object(agt1 obj) has_object(agt2 obj)) eq(agt1 agt2)))))}

end
