functor 

export

 ProcDef

define

  proc {ProcDef Name Body}
    case Name of main then
         Body = seq( check_for(thomas tomato)
                     ifte( exists(t and(obj_is_type(t tomato) neg(used(t))))
                           pcall(makeSalad(bowl(1)))
                           pcall(makeCake(bowl(1)))))
    [] makeSalad(Cont) then
         Body = seq(conc(conc(pcall(chopTypeInto(lettuce Cont))
                           pcall(chopTypeInto(tomato Cont)))
                           pcall(chopTypeInto(carrot Cont)))
                    pick(agt seq(seq(
                         pcall(ensureHas(agt Cont))
                         mix(agt Cont))
                         release(agt Cont))))
    [] makeCake(Cont) then
         Body = seq(conc(conc(pcall(placeTypeInto(flour Cont))
                           pcall(placeTypeInto(sugar Cont)))
                           pcall(placeTypeInto(egg Cont)))
                    pick(agt seq(seq(
                         pcall(ensureHas(agt Cont))
                         mix(agt Cont))
                         release(agt Cont))))
    [] placeTypeInto(Type Cont) then
         Body = pick(agt pick(obj seq( test(obj_is_type(obj Type))
                                  seq( acquire(agt obj)
                                       pcall(placeInto(agt obj Cont))))))
    [] placeInto(Agt Obj Cont) then
        Body = seq( pcall(ensureHas(Agt Obj))
               seq( pcall(ensureHas(Agt Cont))
               seq( place_in(Agt Obj Cont)
                    release(Agt Cont))))
    [] chopTypeInto(Type Cont) then
         Body = pick(agt pick(obj seq( test(obj_is_type(obj Type))
                                       pcall(chopInto(agt obj Cont))
                                  )))
    [] chopInto(Agt Obj Cont) then
         Body = seq(pcall(ensureHas(Agt Obj))
                    pick(myKnife seq( test(and(obj_is_type(myKnife knife)))
                               seq( pcall(ensureHas(Agt myKnife))
                               seq( chop(Agt Obj)
                               seq( pcall(ensureHas(Agt Cont))
                               seq( place_in(Agt Obj Cont)
                               seq( release(Agt myKnife)
                                   either(nil seq(test(true) release(Agt Cont)))
                               )))))
                   )))
    [] ensureHas(Agt Obj) then
         Body = ifte(has_object(Agt Obj) nil acquire(Agt Obj))
    end
  end

end

