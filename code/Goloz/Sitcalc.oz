
functor

import

  LP
  Domain

  Module

export

  Actor

  Uniformize
  Regress

  Ex

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
    assign: proc {$ Vs}
           % TODO: assign values to free variables
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
  Uniformize = {FOF.transformation 'sitcalc.uniformize' Uniformize_atom}
  proc {Uniformize_atom P U}
    U = {FOF.atom P}
  end

  %
  %  Regress the formula over the given action.
  %
  Regress = {FOF.transformation 'sitcalc.regress' Regress_atom}
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

  
  %
  %  Procedures for dealing with executions.
  %  An execution is like a situation with some extra meta-data attached.
  %
  Ex = ex(

    init: proc {$ S E}
            E=ex(nil S)
          end

    append: proc {$ EIn R EOut}
              ex(Rs S) = EIn
              Test = {Value.condSelect R test true}
              Act = {Value.condSelect R action nil}
              Thred = {Value.condSelect R thred nil}
            in
              EOut = ex(r(test:Test action:Act thred:Thred)|Rs S)
            end

    addtest: proc {$ EIn C EOut}
               ex(Run S) = EIn
             in
               case Run of R|Rs then Rp in
                  Rp = {Record.adjoinAt R test and(C R.test)}
                  EOut = ex(Rp|Rs S)
               else
                  EOut = {Ex.append EIn r(test: C)}
               end
             end

    addthred: proc {$ EIn T EOut}
                ex(Run S) = EIn
              in
                case Run of R|Rs then Rp in
                  Rp = {Record.adjoinAt R thred T|R.thred}
                  EOut = ex(Rp|Rs S)
                else EIn = EOut end
              end
  )
  
end

