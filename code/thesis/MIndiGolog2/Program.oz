functor 

export

 ProcDef

define

  proc {ProcDef Name Body}
    case Name of main then
         Body = seq( check_for(joe egg)
                     ifte( exists(e and(obj_is_type(t egg) neg(used(e))))
                           pcall(makeEggSalad(bowl1))
                           pcall(makeVegSalad(bowl1))))
    [] makeVegSalad(Cont) then
         Body = seq(conc(conc(pcall(chopTypeInto(lettuce Cont))
                           pcall(chopTypeInto(tomato Cont)))
                           pcall(chopTypeInto(carrot Cont)))
                    pick(agt seq(seq(
                         pcall(ensureHas(agt Cont))
                         mix(agt Cont))
                         release(agt Cont))))
    [] makeEggSalad(Cont) then
         Body = seq(conc(conc(pcall(chopTypeInto(lettuce Cont))
                           pcall(chopTypeInto(egg Cont)))
                           pcall(chopTypeInto(cheese Cont)))
                    pick(agt seq(seq(
                         pcall(ensureHas(agt Cont))
                         mix(agt Cont))
                         release(agt Cont))))
    [] chopTypeInto(Type Cont) then
         Body = pick(agt pick(obj seq( test(obj_is_type(obj Type))
                                       pcall(chopInto(agt obj Cont))
                                  )))
    [] chopInto(Agt Obj Cont) then
         Body = seq(pcall(ensureHas(Agt Obj))
                    pick(myBoard seq( test(and(obj_is_type(myBoard board)))
                               seq( pcall(ensureHas(Agt myBoard))
                               seq( chop(Agt Obj)
                               seq( pcall(ensureHas(Agt Cont))
                               seq( place_in(Agt Obj Cont)
                               seq( release(Agt myKnife)
                                   either(nil release(Agt Cont))
                               )))))
                   )))
    [] ensureHas(Agt Obj) then
         Body = ifte(has_object(Agt Obj) nil acquire(Agt Obj))
    end
  end

end

