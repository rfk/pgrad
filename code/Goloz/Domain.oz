%
%  Domain.oz:  specifics of the sitcalc domain under operation
%
%  This file specifies the specific dynamics of the domain being executed
%  in, such as successor-state axioms and possibility axioms.
%

functor 

import

  FOF

export

  natural: Natural
  poss: Poss
  agent: Agent
  holds: Holds

define

  proc {Agent A}
    dis  A = thomas
    []      A = richard
    []      A = harriet
    end
  end

  proc {Natural Act}
    dis  Act = ring_timer(_)
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

