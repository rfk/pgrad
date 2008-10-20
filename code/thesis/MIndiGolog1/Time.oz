%
%  Time.oz:  implement time-points as an abstract data type
%
%  Copyright 2008, Ryan Kelly
%
%  Timepoints are an abstract quantity with constraint-handling
%  abilities.  Currently they are implemented as finite domain
%  integers, but I'd like to use a more powerful constraint solver
%  eventually.
%

functor 
import

  FD

export

  Less
  LessEq
  Greater
  GreaterEq
  Decl
  Min
  Max
  Plus
  Minus
  

define

  Less = proc {$ T1 T2}
    T1 <: T2
  end

  LessEq = proc {$ T1 T2}
    T1 =<: T2
  end

  Greater = proc {$ T1 T2}
    T1 >: T2
  end

  GreaterEq = proc {$ T1 T2}
    T1 >=: T2
  end

  Decl = proc {$ T}
      {FD.decl T}
  end

  Min = proc {$ T M}
    if {IsDet T} then M = T
    else M = {FD.reflect.min T} end
  end

  Max = proc {$ T M}
    if {IsDet T} then M = T
    else M = {FD.reflect.max T} end
  end

  Plus = proc {$ T1 T2 T}
    T =: T1 + T2
  end

  Minus = proc {$ T1 T2 T}
    T =: T1 - T2
  end

end

