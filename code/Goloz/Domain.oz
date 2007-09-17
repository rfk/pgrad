%
%  Domain.oz:  specifics of the sitcalc domain under operation
%
%  This file specifies the specific dynamics of the domain being executed
%  in, such as successor-state axioms and possibility axioms.
%

functor 

import

  Sitcalc
  LP

define

  D = Sitcalc.dom

  {D.agent thomas}
  {D.agent richard}
  {D.agent harriet}

  {D.object knife 2}
  {D.object bowl 3}
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

  {D.adfluent poss(acquire) fun {$ _ Obj}
        and(nexists(a has_object(a Obj)) neg(used(Obj)))
        
  end}
  {D.adfluent poss(release) fun {$ Agt Obj}
        has_object(Agt Obj)
  end}
  {D.adfluent poss(transfer) fun {$ Agt Src Dst}
        and(has_object(Agt Src) has_object(Agt Dst))
  end}
  {D.adfluent poss(place_in)  fun {$ Agt Obj Dst}
        and(has_object(Agt Obj) has_object(Agt Dst)
            neg(obj_is_type(Obj appliance)))
            
  end}

  {D.fluent has_object(agent object)}
  {D.fluent used(object)}
  {D.fluent contents(object object)}

  {D.causesTrue has_object acquire fun {$ Agt#Obj Agt#Obj} true end}
  {D.causesFalse has_object release fun {$ Agt#Obj Agt#Obj} true end}
  {D.causesFalse has_object place_in fun {$ Agt#Obj Agt#Obj#_}
        obj_is_type(Obj ingredient)
  end}

  {D.causesTrue used acquire_object fun {$ Obj _#Obj} true end}

  {D.causesTrue contents place_in fun {$ Obj#Conts Agt#OConts#Obj}
      'or'(and(neg(exists(c contents(Obj c))) eq(OConts Conts))
           exists(c and(contents(Obj c) eq(Conts add(OConts c)))a))
  end}
  {D.causesTrue contents transfer fun {$ Obj#Conts Agt#Src#Obj}
      exists(cs and(contents(Src cs)
        'or'(and(neg(exists(c contents(Obj c))) eq(cs Conts))
             exists(c and(contents(Obj c) eq(Conts add(cs c)))))))
  end}

  {D.conflicts proc {$ Act} A1 A2 Obj in
       {LP.member acquire_object(A1 Obj) Act}
       {LP.member acquire_object(A2 Obj) Act}
       (A1 \= A2) = true
  end}

end
