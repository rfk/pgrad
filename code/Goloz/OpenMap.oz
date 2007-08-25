%
%  OpenMap: a name#value mapper with open-ended lists
%

functor 

export

  New
  Map
  Get

define

  proc {New M}
    M = nil
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
      else {Get M2 K V}
    end
  end

end
