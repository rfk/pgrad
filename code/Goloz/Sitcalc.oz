
functor

import

  LP
  Domain
  Time

export

  actor: Actor
  start: Start
  preceeds: Preceeds
  preceeds_eq: PreceedsEq
  legal: Legal
  poss: Poss

define

  proc {Actor Actn Agt}
    {LP.neg proc {$} {Domain.natural Actn} end}
    Agt = Actn.1
  end

  proc {Start S T}
    choice  S = s0  T = 0
    []      S = res(_ T _)
    end
  end

  proc {Preceeds S1 S2}
  C T Sp in
     S2 = res(C T Sp) {Poss C T Sp}
     {PreceedsEq S1 Sp} {Time.lessEq {Start Sp} T}
  end

  proc {PreceedsEq S1 S2}
    choice  S1 = S2
    []      {Preceeds S1 S2}
    end
  end

  proc {Legal S1 S2}
    choice  S1 = S2
    []      C T Sp in S2 = res(C T Sp)
            {Poss C T Sp}
            {Time.lessEq {Start S2} T}
            {LP.neg proc {$} NA T2 in
                {Domain.natural NA}
                {Poss NA T2 S2}
                {Time.lessEq T2 T}
                {LP.neg proc {$}
                  {LP.member NA C}
                end}
            end}
    end
  end

  proc {Poss C T S}
    C = _|_
    {PossAll C T S}
    {LP.neg proc {$} {Domain.conflicts C T S} end}
  end

  proc {PossAll C T S}
    choice  C = nil
    []      A Cs in C = A|Cs {Domain.poss A T S} {PossAll Cs T S}
    end
  end

end

