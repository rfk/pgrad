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
           acquire_object(jim knife1)
    [] doPlaceTypeIn(Agt Type Dest) then
           pick(obj seq(test(obj_is_type(obj Type))
                        seq(acquire_object(Agt obj)
                            pcall(doPlaceIn(Agt obj Dest)))))
    else fail
    end
  end

end
