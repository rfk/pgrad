%
%  Time.oz:  module implementing time-points
%
%  Timepoints are an abstract quantity with constraint-handling
%  abilities.  Currently they are implemented as finite domain
%  integers.  Another option could be as real interval variables
%  using the RI module.
%

functor 
import

  FD

export

  less: Less
  lessEq: LessEq
  greater: Greater
  greaterEq: GreaterEq
  decl: Decl
  

define

  proc {Less T1 T2}
    T1 <: T2
  end

  proc {LessEq T1 T2}
    T1 =<: T2
  end

  proc {Greater T1 T2}
    T1 >: T2
  end

  proc {GreaterEq T1 T2}
    T1 >=: T2
  end

  proc {Decl T}
    {FD.decl T}
  end

end

