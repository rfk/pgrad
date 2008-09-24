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
           seq(conc(acquire(jim bowl1)
               conc(acquire(jim board2)
                    acquire(joe board1)))
               acquire(jim egg1))
           %pcall(makeCakeMix(bowl1))
    [] ensureHas(Agt Obj) then
           ifte(hasObject(Agt Obj) nil acquire(Agt Obj))
    [] doPlaceIn(Agt Obj Dest) then
           seq(conc(pcall(ensureHas(Agt Obj)) pcall(ensureHas(Agt Dest)))
           seq(placeIn(Agt Obj Dest)
               release(Agt Dest)))
    [] doTransfer(Agt Source Dest) then
           seq(conc(pcall(ensureHas(Agt Source)) pcall(ensureHas(Agt Dest)))
           seq(transfer(Agt Source Dest)
               release(Agt Dest)))
    [] doPlaceTypeIn(Agt Type Dest) then
           pick(obj seq(test(objIsType(obj Type))
                        pcall(doPlaceIn(Agt obj Dest))))
    [] makeCakeMix(Dest) then
           seq(conc(pick(agt seq(test(isAgent(agt)) pcall(doPlaceTypeIn(agt egg Dest))))
               conc(pick(agt seq(test(isAgent(agt)) pcall(doPlaceTypeIn(agt flour Dest))))
               conc(pick(agt seq(test(isAgent(agt)) pcall(doPlaceTypeIn(agt sugar Dest))))
               )))
           seq(pick(agt seq(test(isAgent(agt))
                        seq(acquire(agt Dest)
                        seq(beginTask(agt mix(Dest 5))
                            release(agt Dest)
                        )))
               )
           ))
    else fail
    end
  end

end
