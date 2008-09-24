%
%  MIndiGolog.oz:  semantics of MIndiGolog
%

functor

import

    Sitcalc
    LP
    Domain

export

    Script

define

  proc {Trans D S Dp Sp}
      case D of nil then fail
      []   test(Cond) then choice {Sitcalc.holds Cond S} Sp=S Dp=nil
                           [] Tn Cn in {Sitcalc.lntp S Tn}
                                       {Sitcalc.pna S Cn}
                                       Dp=D Sp=res(Cn Tn S)
                           end
      []   seq(D1 D2) then choice D1r in {Trans D1 S D1r Sp} Dp=seq(D1r D2)
                           []            {Final D1 S} {Trans D2 S Dp Sp}
                           end
      []   choose(D1 D2) then choice {Trans D1 S Dp Sp}
                            []       {Trans D2 S Dp Sp}
                            end
      []   pick(V D1) then local D2 in
                               {LP.subInTerm V _ D1 D2}
                               {Trans D2 S Dp Sp}
                            end
      []   star(D1) then local D2 in
                               {Trans D S D2 Sp}
                               Dp=seq(D2 star(D1))
                         end
      []   ifte(Cond D1 D2) then choice {Sitcalc.holds Cond S}
                                        {Trans D1 S Dp Sp}
                                 []     {Sitcalc.holds neg(Cond) S}
                                        {Trans D2 S Dp Sp}
                                 end
      []   wloop(Cond D1) then local D2 in
                                 {Sitcalc.holds Cond S}
                                 {Trans D1 S D2 Sp}
                                 Dp=seq(D2 wloop(Cond D1))
                               end
      []   conc(D1 D2) then choice D1r D2r C1 C2 CT T in
                                     {Step D1 S D1r res(C1 T S)}
                                     {Step D2 S D2r res(C2 T S)}
                                     {LP.neg proc {$} A in
                                        {LP.member A C1}
                                        {LP.member A C2}
                                        {LP.neg proc {$} {Domain.isExog A} end}
                                     end}
                                     {Union C1 C2 CT}
                                     {Poss CT T S}
                                     Sp=res(CT T S) Dp=conc(D1r D2r)
                            []     D1r in {Trans D1 S D1r Sp} Dp=conc(D1r D2)
                            []     D2r in {Trans D2 S D2r Sp} Dp=conc(D1 D2r)
                            end
      []   pconc(D1 D2) then choice D1r in {Trans D1 S D1r Sp} Dp=pconc(D1r D2)
                             []     D2r in {Trans D2 S D2r Sp} Dp=pconc(D1 D2r)
                                    {LP.neg proc {$} {Trans D1 S _ _} end}
                             end
      []   cstar(D1) then local D2 in
                              {Trans D1 S D2 Sp}
                              Dp=conc(D2 cstar(D1))
                          end
      []   pcall(D1) then local Body D2 in
                            {LP.subInTerm now S D1 D2}
                            {Proc D2 Body}
                            {Trans Body S Dp Sp}
                          end
      else local D1 C T in
              {LP.subInTerm now S D D1}
              {Sitcalc.toConcAct D1 C}
              choice Tn={Sitcalc.lntp S}
                     Cn={Sitcalc.pna S}
                   in
                     {Time.greaterEq T {Sitcalc.start S}}
                     choice %% Can do before LNTP actions
                            {Time.less T Tn}
                            {Sitcalc.legal C T S}
                            Sp=res(C T S) Dp=nil
                     []     %% Can with with LNTP actions
                            Cu={LP.union C Cn} in
                            {Sitcalc.legal Cu Tn S}
                            Sp=res(Cu Tn S) Dp=nil
                     []     %% Can do LNTP actions first
                            Sp=res(Cn Tn S) Dp=D
                     end
              []     {LP.neg proc {$} {Sitcalc.lntp S _} end}
                     {Sitcalc.legal C T S}
                     Sp=res(C T S) Dp=nil
              end
           end
      end
  end

  proc {Final D S}
      case D of nil then skip
      []   seq(D1 D2) then {Final D1 S} {Final D2 S}
      []   choose(D1 D2) then choice {Final D1 S} [] {Final D2 S} end
      []   pick(V D1) then local D2 in {SubInProg V _ D1 D2} {Final D2 S} end
      []   star(_) then skip
      []   ifte(Cond D1 D2) then
                     choice {Sitcalc.holds Cond S} {Final D1 S}
                     []     {Sitcalc.holds neg(Cond) S} {Final D2 S}
                     end
      []   wloop(Cond D1) then
                     choice {Sitcalc.holds neg(Cond) S}
                     []     {Final D1 S}
                     end
      []   conc(D1 D2) then {Final D1 S} {Final D2 S}
      []   pconc(D1 D2) then {Final D1 S} {Final D2 S}
      []   cstar(_) then skip
      []   pcall(D1) then local D2 D3 in
                            {LP.subInTerm now S D1 D2}
                            {Proc D2 D3}
                            {Final D3 S}
                          end
      else fail
      end
  end

  proc {TransStar D S Dp Sp}
    choice  Dp=D Sp=S
    []      Dr Sr in {Trans D S Dr Sr} {TransStar Dr Sr Dp Sp}
    end
  end

  proc {Step D S Dp Sp}
    choice Sp=res(_ _ S) {Trans D S Dp Sp}
    []     Dr in {Trans D S Dr S} {Step Dr S Dp Sp}
    end
  end

  proc {Do D S Sp}
     Dp
  in
     {TransStar D S Dp Sp}
     {Final Dp Sp}
  end

  proc {Proc Nm Body}
    case Nm of doPlaceTypeIn(Agt Type Dest) then
               Body=pi(obj seq(test(obj_is_type(obj Type))
                               seq(acquire_object(Agt obj)
                                   pcall(doPlaceIn(Agt obj Dest)))))
    end
  end


  proc {Poss A T S}
    local Start in
      Start={ToRIVar {SitStart S}}
      {RI.lessEq Start T}
    end
    choice (A\=nil)=true {PossAll A T S}  % TODO: conflicts/3
    []     Agt Obj in A=acquire_object(Agt Obj)
                      {Holds.no has_object(_ Obj) S}
                      {Holds.no doing_task(Agt _ _) S}
                      {Holds.no used(Obj) S}
    []     Agt Obj in A=release_object(Agt Obj)
                      {Holds.yes has_object(Agt Obj) S}
                      {Holds.no doing_task(Agt _ _) S}
    []     Agt ID in A=set_timer(Agt ID _)
                     {Holds.no timer_set(ID _) S}
                     {Holds.no doing_task(Agt _ _) S}
    []     ID in A=ring_timer(ID)
                 {Holds.yes timer_set(ID T) S}
    end
  end


  /*  Holds - determine whether fluents hold in a situation
   *
   *  This is a record with special features yes and no, used to 
   *  determine whether a fluent is true: {Holds.yes F S} to assert
   *  that fluent F is true in situation S.
   *
   *  Holds also has a feature for each fluent in the domain, which
   *  is in turn a record with features named plus, minus, and init.
   *  Init asserts that the fluent is true of the initial situation,
   *  plus asserts that the fluent became true in a situation, and
   *  minus asserts that the fluent become false in a situation.
  */
  Holds=holds(

    yes: proc {$ F S}
           local FName FProc in
             {Label F FName}
             {CondSelect Holds FName nil FProc}
             if FProc==nil then
               fail
             else
               choice S=s0
                      {FProc.init F}
               []     {FProc.plus F S}
               []     Sp in S=res(_ _ Sp) {Holds.yes F Sp}
                      {NegAsFail proc {$} {FProc.minus F S} end}
               end
             end
           end
         end

    no: proc {$ F S}
          {NegAsFail proc {$} {Holds.yes F S} end}
        end

    has_object: fluent(

       plus: proc{$ has_object(Agt Obj) S}
               local C in
                 S=res(C _ _)
                 {IsMember acquire_object(Agt Obj) C}
               end
             end

       minus: proc{$ has_object(Agt Obj) S}
               local C in
                 S=res(C _ _)
                 choice {IsMember release_object(Agt Obj) C}
                 []     {Holds.yes used(Obj) S}
                 end
               end
              end

      init: proc{$ F} fail end
    )

    used:  fluent(

      plus: proc{$ used(Obj) S}
              {ObjIsType Obj ingredient}
              local C in
                S=res(C _ _)
                {IsMember place_in(_ Obj _) C}
              end
            end

      minus: proc{$ F S}
               fail
             end

      init: proc{$ F}
              fail
            end
    )

    timer_set:  fluent(

      plus: proc{$ timer_set(ID RingTime) S}
              local C Dur RIDur RIStart RIRT in
                S=res(C _ _)
                {IsMember set_timer(_ ID Dur) C}
                RIDur={ToRIVar Dur}
                RIRT={ToRIVar RingTime}
                RIStart={ToRIVar {SitStart S}}
                {RI.plus RIDur RIStart RIRT}
              end
            end

      minus: proc{$ timer_set(ID _) S}
               local C in 
                 S=res(C _ _)
                 {IsMember ring_timer(ID) C}
               end
             end

      init: proc{$ F} fail end
    )
  )

end
