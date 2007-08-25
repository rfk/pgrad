%
%  Domain.oz:  specifics of the sitcalc domain under operation
%
%  This file specifies the specific dynamics of the domain being executed
%  in, such as successor-state axioms and possibility axioms.
%

functor 

export

  Agent
  Object
  Natural
  Dfluent
  Regress
  BGAxioms

define

  proc {Agent A}
    dis  A = thomas
    []   A = richard
    []   A = harriet
    end
  end

  proc {Object O}
    dis  O = knife1
    []   O = knife2
    []   O = knife3
    []   O = board1
    []   O = board2
    []   O = bowl1 
    []   O = bowl2
    []   O = bowl3
    []   O = oven
    end
  end

  proc {BGAxioms Ls}
    Ls = [all(agt1 all(agt2 all(obj impl(neg(eq(agt1 agt2)) disj(neg(holding(agt1 obj)) neg(holding(agt2 obj)))))))]
  end

  proc {Natural Act}
    dis  Act = ring_timer(_)
    []   Act = end_task(_)
    end
  end

  proc {Dfluent F D}
    D = true
  end

  proc {Regress P A F}
    F = P
  end

end

