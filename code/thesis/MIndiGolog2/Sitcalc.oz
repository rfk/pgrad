%
%  Sitcalc.oz:  procedure for domain-independent sitcalc stuff
%

functor

import

  LP
  Step
  Domain

  Search
  System

export

  Actor
  Legal
  Holds
  HoldsR
  Outcomes

define

  %  Get the agent performing a given action
  %
  proc {Actor Actn Agt}
    Agt = Actn.1
  end

  proc {Legal C S}
    {Poss C S}
  end

  % Generic possibility predicate - succeeds if C is not empty, each action
  % is individually possible, and they don't conflict.
  %
  proc {Poss C S}
    C = _|_
    {PossAll C S}
    {LP.neg proc {$} Cl Sl in
        (Cl#Sl) = {LP.copyTerm (C#S)}
        {Domain.conflicts Cl Sl}
     end}
  end

  proc {PossAll C S}
    choice  C = nil
    []      A Cs in C = A|Cs {Domain.poss A S} {PossAll Cs S}
    end
  end

  % Determine whether a fluent holds in a given history
  %
  proc {Holds F H}
    {HoldsR F nil H}
  end

  % Determine whether a fluent holds in a given history, assuming sensing
  % results as given by SR.
  %
  proc {HoldsR F SR H}
    % Reduce the formula down to NNF
    case F of conj(F1 F2) then {HoldsR F1 SR H} {HoldsR F2 SR H}
    []   disj(F1 F2) then choice {HoldsR F1 SR H} [] {HoldsR F2 SR H} end
    []   all(Var F1) then {HoldsR neg(ex(Var neg(F1))) SR H}
    []   ex(Var F1) then F2 in {LP.subInTerm Var _ F1 F2}
                               {HoldsR F2 SR H}
    []   neg(F1) then case F1 of all(Var F2) then {HoldsR ex(Var neg(F2)) SR H}
                      []   disj(F2 F3) then {HoldsR conj(neg(F2) neg(F3)) SR H}
                      []   conj(F2 F3) then {HoldsR disj(neg(F2) neg(F3)) SR H}
                      []   neg(F2) then {HoldsR F2 SR H}
                      []   ex(Var F2) then
                               {LP.neg proc {$} F3 in
                                 {LP.subInTerm Var _ {LP.copyTerm F2} F3}
                                 {HoldsR F3 {LP.copyTerm SR} {LP.copyTerm H}}
                               end}
                      else {LP.neg proc {$}
                               {HoldsR {LP.copyTerm F1} {LP.copyTerm SR} {LP.copyTerm H}}
                           end}
                      end
    % Then call into either SSA or Init
    else case H of now then
                {Domain.init F SR}
         [] ex(Step H2) then SR2 in 
                {Domain.addSensingResults SR Step.out SR2}
                {Domain.ssa F [Step.action] SR2 H2}
         end
    end
  end

  proc {Outcomes S Outs}
    Outs = {Search.base.all proc {$ OutStep} O in
      {Domain.outcome S.action O}
      OutStep = {Step.setout S O}
    end}
  end

end
