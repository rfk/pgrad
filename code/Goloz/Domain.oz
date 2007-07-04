
functor 
import

  Time
  LP
  Sitcalc

export

  natural: Natural
  poss: Poss
  agent: Agent
  holds: Holds

define

  proc {Agent A}
    choice  A = thomas
    []      A = richard
    []      A = harriet
    end
  end

  proc {Natural Act}
    choice  Act = ring_timer(_)
    []      Act = end_task(_)
    end
  end

  proc {Poss A T S}
    skip
  end

  proc {Holds F S}
    skip
  end

end

