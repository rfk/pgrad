functor 

export

 ProcDef

define

  proc {ProcDef Name Body}
    case Name of main then
         Body = pcall(makeSalad(bowl(1)))
    [] makeSalad(Cont) then
         Body = seq(conc(conc(pcall(chopTypeInto(lettuce Cont))
                           pcall(chopTypeInto(tomato Cont)))
                           pcall(chopTypeInto(carrot Cont)))
                    pick(agt seq(seq(
                         pcall(ensureHas(agt Cont))
                         mix(agt Cont))
                         release(agt Cont))))
    [] chopTypeInto(Type Cont) then
         Body = pick(agt pick(obj seq( test(obj_is_type(obj Type))
                                  seq( acquire(agt obj)
                                       pcall(chopInto(agt obj Cont))
                                  ))))
    [] chopInto(Agt Obj Cont) then
         Body = seq(pcall(ensureHas(Agt Obj))
                    pick(myBoard seq( test(and(obj_is_type(myBoard board)
                                             nexists(c contents(myBoard c))))
                    pick(myKnife seq( test(and(obj_is_type(myKnife knife)))
                               seq( pcall(ensureHas(Agt myBoard))
                               seq( pcall(ensureHas(Agt myKnife))
                               seq( place_in(Agt Obj myBoard)
                               seq( chop(Agt myBoard)
                               seq( pcall(ensureHas(Agt Cont))
                               seq( transfer(Agt myBoard Cont)
                               seq( release(Agt myBoard)
                                    release(Agt Cont)  
                               )))))))))
                   )))
    [] ensureHas(Agt Obj) then
         Body = ifte(has_object(Agt Obj) nil acquire(Agt Obj))
    end
  end

end

