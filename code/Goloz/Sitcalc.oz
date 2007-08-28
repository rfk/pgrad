
functor

import

  LP
  Domain

  Module

export

  Actor

  Uniformize
  Regress

define

  %
  %  Create our private FOF reasoning module.
  %  We delegate determination of WFF to the Domain module.
  %
  FOF = _
  {Module.link ['FOF.ozf'] [FOF]}
  FOF.lang = lang(
    wff: proc {$ P}
           % TODO: ensure well-formedness of predicates
           skip
         end
  )

  %
  %  Extract the actor from a given action.
  %  Fails if the action is exogenous.
  %
  proc {Actor Actn Agt}
    {LP.neg proc {$} {Domain.natural Actn} end}
    Agt = Actn.1
  end

  %
  %  Flatten defined fluents according to their definitions in the domain
  %
  proc {Uniformize F U}
    {FOF.memoCall 'sitcalc.uniformize' M_Uniformize [F] U}
  end
  proc {M_Uniformize Args U}
    [F] = Args
  in
    {FOF.transform Uniformize_atom R_Uniformize nil F U}
  end
  proc {R_Uniformize F _ U}
    {Uniformize F U}
  end
  proc {Uniformize_atom P _ U}
    {FOF.memoCall 'sitcalc.uniformize_atom' M_Uniformize_atom [P] U}
  end
  proc {M_Uniformize_atom Args U}
    [P] = Args
  in
    U = {FOF.atom P}
  end

  %
  %  Regress the formula over the given action.
  %
  proc {Regress F A R}
    {FOF.memoCall 'sitcalc.regress' M_Regress [F A] R}
  end
  proc {M_Regress Args R}
    [F A] = Args
    Rp
  in
    {FOF.transform Regress_atom Regress A F Rp}
    {FOF.simplify Rp R}
  end
  proc {Regress_atom P A U}
    EpsP EpsN
  in
    EpsP = {Domain.causes_true A P}
    EpsN = {Domain.causes_false A P}
    U = {FOF.simplify {FOF.parseRecord 'or'(EpsP and(P neg(EpsN)))}}
  end

  %
  %  Determine whether the given formula holds in the given
  %  situation.
  %
  proc {Holds F S B}
    case S of res(C Sr) then Fr = {Regress F C} in B={Holds Fr Sr}
    else B={HoldsInit F}
    end
  end

  proc {HoldsInit F B}
    {FOF.tautology_e F _ B}
  end
  
end

