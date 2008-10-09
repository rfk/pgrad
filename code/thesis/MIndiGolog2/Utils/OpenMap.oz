%
%  OpenMap: an open-ended record->value mapper
%
%

functor 

export

  New
  Map
  Get

  Test

define

  proc {New M}
    M = _
  end

  proc {Map M K V}
    if {IsFree M} then
      M = K#V|_
    else
      K2#V2|M2 = M in
      if K == K2 then V = V2
      else {Map M2 K V} end
    end
  end

  proc {Get M K V}
    if {IsFree M} then
      V = nil
    else
      K2#V2|M2 = M in
      if K == K2 then V = [V2]
      else {Get M2 K V} end
    end
  end

  proc {Test}
    M = {New}
    V1
  in
    {IsFree M true}
    {Get M a nil}
    {Get M a(t1 t2) nil}
    {Map M a 3}
    {Get M a [3]}
    {Get M a(t1 t2) nil}
    {Map M a(t1) V1}
    {Map M b 1}
    local V in
       {Map M a V}
       V = 3
    end
    {Get M a(t1) [V1]}
    {IsFree V1 true}
    V1 = 2
    {Map M a(t1) 2}
  end

end
