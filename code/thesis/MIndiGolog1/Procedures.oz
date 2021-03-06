%
%  Procedures.oz:  definitions of procedures for the domain
%
%  Copyright 2008, Ryan Kelly
%
%  This file provides a single function {Procdef}, which takes a
%  MIndiGolog procedure call as input and returns the corresponding
%  procedure body as output.
%
%

functor

import

export

  Procdef

define

  fun {Procdef Nm}
    case Nm of main then
          pcall(makeSalad(bowl1))
          %search(pcall(hardToPlan))
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
                        seq(beginTask(Agt chop(brd))
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
    [] makeCakeMix(Dest) then
           seq(conc(pick(agt seq(test(isAgent(agt))
                             pcall(placeTypeIn(agt egg Dest))))
               conc(pick(agt seq(test(isAgent(agt))
                             pcall(placeTypeIn(agt flour Dest))))
                    pick(agt seq(test(isAgent(agt))
                             pcall(placeTypeIn(agt sugar Dest))))
               ))
               pick(agt seq(test(isAgent(agt))
                        seq(acquire(agt Dest)
                        seq(beginTask(agt mix(Dest 5))
                            release(agt Dest)
                        )))
               )
           )
    [] makeSalad(Dest) then
          seq(conc(pick(a seq(test(isAgent(a))
                              pcall(chopTypeInto(a lettuce Dest))))
              conc(pick(a seq(test(isAgent(a))
                              pcall(chopTypeInto(a tomato Dest))))
                   pick(a seq(test(isAgent(a))
                              pcall(chopTypeInto(a carrot Dest))))
              ))
              pick(a seq(test(isAgent(a))
                     seq(pcall(ensureHas(a Dest))
                     seq(beginTask(a mix(Dest 1))
                         release(a Dest)
                     )))
              )
          )
    [] acquireType(Agt Type) then
          pick(obj seq(test(objIsType(obj Type))
                           acquire(Agt obj)
          ))
    [] hardToPlan then
          seq(pcall(acquireType(joe carrot))
          seq(pcall(acquireType(jon sugar))
          seq(pcall(acquireType(jim lettuce))
          seq(pcall(acquireType(joe flour))
          seq(pcall(acquireType(jon flour))
          seq(test(hasObject(joe carrot3))
          seq(test(hasObject(joe flour5))
              test(hasObject(jon sugar4))
          )))))))
    else fail
    end
  end

end
