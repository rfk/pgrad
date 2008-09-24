%
%  Procedures.oz:  definitions of procedures for the domain
%

functor

import

export

define

  proc {Proc Nm Body}
    case Nm of doPlaceTypeIn(Agt Type Dest) then
               Body=pick(obj seq(test(obj_is_type(obj Type))
                               seq(acquire_object(Agt obj)
                                   pcall(doPlaceIn(Agt obj Dest)))))
    end
  end

end
