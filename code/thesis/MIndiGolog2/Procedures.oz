%
%  Procedures.oz:  definitions of procedures for the domain
%

functor

import

export

  Procdef

define

  fun {Procdef Nm}
    case Nm of main then
          pcall(makeSalad(bowl1))
    [] ensureHas(Agt Obj) then
           ifte(hasObject(Agt Obj) nil acquire(Agt Obj))
    [] doPlaceIn(Agt Obj Dest) then
           seq(pcall(ensureHas(Agt Obj))
           seq(pcall(ensureHas(Agt Dest))
           seq(placeIn(Agt Obj Dest)
               release(Agt Dest))))
    [] doTransfer(Agt Source Dest) then
           seq(pcall(ensureHas(Agt Source))
           seq(pcall(ensureHas(Agt Dest))
           seq(transfer(Agt Source Dest)
               release(Agt Dest))))
    [] placeTypeIn(Agt Type Dest) then
           pick(obj seq(test(objIsType(obj Type))
                        pcall(doPlaceIn(Agt obj Dest))))
    [] chopInto(Agt Obj Dest) then
           seq(pcall(ensureHas(Agt Obj))
               pick(brd seq(test(conj(objIsType(brd board)
                                      neg(ex(c contents(brd c)))))
                        seq(pcall(ensureHas(Agt brd))
                        seq(placeIn(Agt Obj brd)
                        seq(chop(Agt brd)
                        seq(pcall(ensureHas(Agt Dest))
                        seq(transfer(Agt brd Dest)
                        seq(release(Agt Dest)
                            release(Agt brd)
                        )))))))
               )
           )
    [] chopTypeInto(Agt Type Dest) then
           pick(obj seq(test(objIsType(obj Type))
                        pcall(chopInto(Agt obj Dest))))
    [] makeSalad(Dest) then
          seq(conc(pick(a seq(test(isAgent(a))
                              pcall(chopTypeInto(a lettuce Dest))))
                   seq(pick(a seq(test(isAgent(a)) checkFor(a egg)))
                       ifte(used(egg1)
                            conc(pick(a seq(test(isAgent(a))
                                            pcall(chopTypeInto(a tomato Dest))))
                                 pick(a seq(test(isAgent(a))
                                            pcall(chopTypeInto(a carrot Dest))))
                      
                            )
                            conc(pick(a seq(test(isAgent(a))
                                            pcall(chopTypeInto(a egg Dest))))
                                 pick(a seq(test(isAgent(a))
                                            pcall(chopTypeInto(a cheese Dest))))
                            )
                       )
                   )
              )
              pick(a seq(test(isAgent(a))
                     seq(pcall(ensureHas(a Dest))
                     seq(mix(a Dest)
                         release(a Dest)
                     )))
              )
          )
    [] makeVegSalad(Dest) then
          seq(conc(pick(a seq(test(isAgent(a))
                              pcall(chopTypeInto(a carrot Dest))))
              conc(pick(a seq(test(isAgent(a))
                              pcall(chopTypeInto(a tomato Dest))))
                   pick(a seq(test(isAgent(a))
                              pcall(chopTypeInto(a lettuce Dest))))
              ))
              pick(a seq(test(isAgent(a))
                     seq(pcall(ensureHas(a Dest))
                     seq(mix(a Dest)
                         release(a Dest)
                     )))
              )
          )
    [] makeEggSalad(Dest) then
          seq(conc(pick(a seq(test(isAgent(a))
                              pcall(chopTypeInto(a egg Dest))))
              conc(pick(a seq(test(isAgent(a))
                              pcall(chopTypeInto(a cheese Dest))))
                   pick(a seq(test(isAgent(a))
                              pcall(chopTypeInto(a lettuce Dest))))
              ))
              pick(a seq(test(isAgent(a))
                     seq(pcall(ensureHas(a Dest))
                     seq(mix(a Dest)
                         release(a Dest)
                     )))
              )
          )
    [] acquireType(Agt Type) then
          pick(obj seq(test(objIsType(obj Type))
                           acquire(Agt obj)
          ))
    else fail
    end
  end

end
