%
%  Sitcalc.oz:  procedure for domain-independent sitcalc stuff
%

functor

import

  LP at '/storage/uni/pgrad/code/thesis/MIndiGolog1/LP.ozf'
  Domain at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Domain.ozf'
  Time at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Time.ozf'

  Search

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
    {LP.neg proc {$} An Tn Sl Cl Tl in
      (Sl#Tl) = {LP.copyTerm (S#T)}
      {Domain.isNatural An}
      {Domain.poss An Tn Sl}
      {Time.lessEq Tn Tl}
      {LP.neg proc {$}
          Cl = {LP.copyTerm C}
          {LP.member An Cl}
      end}
    end}
  end

  %  Determine LNTP of situation S1
  %
  proc {LNTP S Tn}
    proc {PotentialLNTP Tnp} An Sl in
      Sl = {LP.copyTerm S}
      {Domain.isNatural An}
      {Domain.poss An Tnp Sl}
    end
  in
    [Tn] = {Search.base.best PotentialLNTP proc {$ BestSoFar Tnp}
        ({Time.min Tnp} < {Time.min BestSoFar}) = true
    end}
  end

  % Determine PNA of situation S1
  proc {PNA S Cn}
    Tn = {LNTP S}
  in
    Cn = {Search.base.all proc {$ A}
           {Domain.isNatural A}
           {Domain.poss A {LP.copyTerm Tn} {LP.copyTerm S}}
         end}
  end

  % Generic possibility predicate - succeeds if C is not empty, each action
  % is individually possible,  and they don't conflict.
  %
  proc {Poss C T S}
    C = _|_
    {PossAll C T S}
    {LP.neg proc {$} Cl Tl Sl in
        (Cl#Tl#Sl) = {LP.copyTerm (C#T#S)}
        {Domain.conflicts Cl Tl Sl}
     end}
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
    try S1 = S2 L = nil
    catch _ then C T Sp in
      S2 = res(C T Sp)
      L = {List.append {ToStepsList S1 Sp} [(C#T)]}
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
                                 {LP.subInTerm Var _ {LP.copyTerm F2} F3}
                                 {Holds F3 {LP.copyTerm S}}
                               end}
                      else {LP.neg proc {$}
                               {Holds {LP.copyTerm F1} {LP.copyTerm S}}
                           end}
                      end
    % Then call into either SSA or Init
    else case S of s0 then
                {Domain.init F}
         [] res(C T Sp) then
                {Domain.ssa F C T Sp}
         end
    end
  end

end

