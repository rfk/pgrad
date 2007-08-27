%
%  ListDict: dictionary whose keys are lists of records.
%
%  Currently only supports the get/put/exchange set of methods.
%

functor 

import

  OpenMap

export

  New
  Get
  CondGet
  Put
  Exchange
  CondExchange

  Test

define

  proc {New D}
    D = ld(o: {OpenMap.new} n: {Cell.new nil})
    {Cell.assign D.n nil}
  end

  proc {Get D Ls V}
    case Ls of nil then V2 = {Cell.access D.n} in
        if V2 == nil then raise system end
        else [V] = V2 end
    else H|Ts = Ls  D2 = {OpenMap.get D.o H} in
        if D2 == nil then raise system end
        else [D2p] = D2 in V = {Get D2p Ts} end
    end
  end

  proc {CondGet D Ls Vd V}
    case Ls of nil then V2 = {Cell.access D.n} in
        if V2 == nil then V = Vd
        else [V] = V2 end
    else H|Ts = Ls  D2 = {OpenMap.get D.o H} in
        if D2 == nil then V = Vd
        else [D2p] = D2 in V = {CondGet D2p Ts Vd} end
    end
  end

  proc {Put D Ls V}
    case Ls of nil then {Cell.assign D.n [V]}
    else H|Ts = Ls  D2 = {OpenMap.map D.o H} in
        if {IsFree D2} then {New D2} end
        {Put D2 Ts V}
    end
  end

  proc {Exchange D Ls Vout Vin}
    if Ls == nil then Vold Vnew in
        {Cell.exchange D.n Vold Vnew}
        if Vold == nil then Vnew = nil raise system end
        else [Vout] = Vold [Vin] = Vnew end
    else H|Ts = Ls  D2 = {OpenMap.map D.o H} in
        if {IsFree D2} then {New D2} end
        {Exchange D2 Ts Vout Vin}
    end
  end

  proc {CondExchange D Ls Vd Vout Vin}
    if Ls == nil then Vold in
        {Cell.exchange D.n Vold [Vin]}
        if Vold == nil then Vout = Vd
        else [Vout] = Vold end
    else H|Ts = Ls  D2 = {OpenMap.map D.o H} in
        if {IsFree D2} then {New D2} end
        {CondExchange D2 Ts Vd Vout Vin}
    end
  end


  proc {Test}
    D = {New}
    V1
    L1 = [a b c]
    L2 = [a c]
  in
    try
      {Get D L1 V1}
      raise testfailed(1) end
    catch E then 
      case E of testfailed(_) then raise E end else skip end
    end
    {CondGet D L1 nil nil}
    {Put D L1 1}
    {CondGet D L1 nil 1}
    {Get D L1 1}
    {Exchange D L1 1 V1}
    {CondExchange D L2 bob bob bill}
    {IsFree V1 true}
    V1 = 2
    {Get D L1 2}
    {Get D L2 bill}
  end

end
