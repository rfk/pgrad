%
%  Sitcalc.oz:  procedure for domain-independent sitcalc stuff
%

functor

import

  LP
  Domain
  Time
  Search
  System

export

  Actor
  Start
  Preceeds
  PreceedsEq
  Legal
  ToConcAct
  ToStepsList
  lntp: LNTP
  pna: PNA
  Holds

define

  %  Get the agent performing a given action
  %
  proc {Actor Actn Agt}
    {LP.neg proc {$} {Domain.isNatural Actn} end}
    Agt = Actn.1
  end

  %  Get the start time of a given situation
  %
  proc {Start S T}
    choice  S = s0  T = 0
    []      S = res(_ T _)
    end
  end

  %  Assert that situation S1 preceeds situation S2
  %
  proc {Preceeds S1 S2}
    C T Sp
  in
    S2 = res(C T Sp) {Poss C T Sp}
    {PreceedsEq S1 Sp} {Time.lessEq {Start Sp} T}
  end

  %  Assert that situation S1 preceeds or is equal to situation S2
  %
  proc {PreceedsEq S1 S2}
    choice  S1 = S2
    []      {Preceeds S1 S2}
    end
  end

  proc {Legal C T S}
    {Poss C T S}
    {Time.less {Start S} T}
    {LP.neg proc {$} An Tn in
      {Domain.isNatural An}
      {Domain.poss An Tn S}
      {Time.lessEq Tn T}
      {LP.neg proc {$}
            {LP.member An C}
      end}
    end}
  end

  %  Determine LNTP of situation S1
  %
  proc {LNTP S Tn}
    An
  in
    {Domain.isNatural An}
    {Domain.poss An Tn S}
    Tn = {Time.min Tn}
    {LP.neg proc {$} An2 Tn2 in
      {Domain.isNatural An2}
      {Domain.poss An2 Tn2 S}
      {Time.less Tn2 Tn}
    end}
  end

  % Determine PNA of situation S1
  proc {PNA S Cn}
    Tn = {LNTP S}
  in
    Cn = {Search.base.all proc {$ A}
           {Domain.isNatural A}
           {Domain.poss A Tn S}
         end}
  end

  % Generic possibility predicate - succeeds if C is not empty, each action
  % is individually possible,  and they don't conflict.
  %
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

  % Convert a lone action term into a proper concurrent action
  %
  proc {ToConcAct A C}
    choice A=_|_ C=A
    []     C = [A]
    end
  end

  % Convert two situations to a list of steps necessary to get from S1 to S2
  %
  proc {ToStepsList S1 S2 L}
    if S1 == S2 then
      L = nil
    else C T Sp in
      S2 = res(C T Sp)
      L = (C#T)|{ToStepsList S1 Sp}
    end
  end

  % Determine whether a fluent holds in a given situation
  %
  proc {Holds F S}
    % Reduce the formula down to NNF
    case F of conj(F1 F2) then {Holds F1 S} {Holds F2 S}
    []   disj(F1 F2) then choice {Holds F1 S} [] {Holds F2 S} end
    []   all(Var F1) then {Holds neg(ex(Var neg(F1))) S}
    []   ex(Var F1) then F2 in {LP.subInTerm Var _ F1 F2}
                               {Holds F2 S}
    []   neg(F1) then case F1 of all(Var F2) then {Holds ex(Var neg(F2)) S}
                      []   disj(F2 F3) then {Holds conj(neg(F2) neg(F3)) S}
                      []   conj(F2 F3) then {Holds disj(neg(F2) neg(F3)) S}
                      []   neg(F2) then {Holds F2 S}
                      []   ex(Var F2) then
                               {LP.neg proc {$} F3 in
                                 {LP.subInTerm Var _ F2 F3}
                                 {Holds F3 S}
                               end}
                      else {LP.neg proc {$}
                               {Holds F1 S}
                           end}
                      end
    % Then call into either SSA or Init
    else choice S=s0
                {Domain.init F}
         [] C T Sp in S=res(C T Sp)
                {Domain.ssa F C T Sp}
         end
    end
  end

end

