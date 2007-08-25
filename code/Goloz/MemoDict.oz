%
%  RDict.oz:  dictionary that can use arbitrary determined records as keys
%

functor 

export

  New
  Get
  CondGet
  Put
  Exchange
  CondExchange

define

  proc {New D}
    {Dictionary.new D}
  end

  proc {Get D K V}
    {Dictionary.get D K V}
  end

  proc {CondGet D K V1 V}
    {Dictionary.condGet D K V1 V}
  end

  proc {Put D K V}
    {Dictionary.put D K V}
  end

  proc {Exchange D K Vout Vin}
    {Dictionary.exchange D K Vout Vin}
  end

  proc {CondExchange D K V1 Vout Vin}
    {Dictionary.condExchange D K V1 Vout Vin}
  end

end
