
declare

functor Goloz

import

    RI at '/opt/mozart/cache/x-ozlib/ri/RI.ozf'
    Search at 'x-oz://system/Search'

export

    Script

define

  proc {ToRIVar Val RIVal}
    if {RI.isRI Val} then
      Val=RIVal
    else
      if {IsDet Val} then
        RIVal={RI.var.exp Val}
      else
        %%  TODO: is this the right thing to do?
        RIVal=Val
      end
    end
  end

  proc {IsMember Elem List}
    choice List=nil fail
    []     List=Elem|_
    []     NewList in List=_|NewList {IsMember Elem NewList}
    end
  end

  proc {NegAsFail P}
    {Search.base.one proc {$ L} {P} L=unit end $} = nil 
  end

  proc {GetActor Actn Agt}
    {IsPrimAction Actn}
    {NegAsFail proc {$} {IsNatural Actn} end}
    Agt=Actn.1
  end

  proc {SitStart S T}
    choice S=s0 T=0
    []     S=res(_ T _)
    end
  end

  proc {Preceeds S1 S2}
    choice S2=s0 fail
    []     C T Sp in S2=res(C T Sp) {Poss C T Sp}
           {PreceedsEq S1 Sp} {RI.lessEq {SitStart Sp} T}
    end
  end

  proc {PreceedsEq S1 S2}
    choice S1=S2
    []     {Preceeds S1 S2}
    end
  end

  proc {PossAll C T S}
    choice C=nil
    []     Head Tail in C=Head|Tail {Poss Head T S} {PossAll Tail T S}
    end
  end

  proc {LNTP S T}
     A FindOthers RIT RIStart
  in
      {ToRIVar T RIT} {ToRIVar {SitStart S} RIStart}
      {IsNatural A} {Poss A T S} {RI.lessEq RIStart RIT}
      FindOthers=proc{$}
               local A2 T2 in
                 {IsNatural A2}
                 {Poss A2 T2 S}
                 {RI.greater RIT T2}
               end
             end
      {NegAsFail FindOthers}
  end

  proc {ToCAct A C}
    if A==_|_ then
        C=A
    else
        C=[A]
    end
  end

  proc {Final D S}
      case D of nil then skip
      []   seq(D1 D2) then {Final D1 S} {Final D2 S}
      []   pick(D1 D2) then choice {Final D1 S} [] {Final D2 S} end
      []   pi(V D1) then local D2 in {SubInProg V _ D1 D2} {Final D2 S} end
      []   start(_) then skip
      []   ifte(Cond D1 D2) then
                     choice {Holds.yes Cond S} {Final D1 S}
                     []     {Holds.no Cond S} {Final D2 S}
                     end
      []   wloop(Cond D1) then
                     choice {Holds.no Cond S}
                     []     {Final D1 S}
                     end
      []   conc(D1 D2) then {Final D1 S} {Final D2 S}
      []   pconc(D1 D2) then {Final D1 S} {Final D2 S}
      []   cstar(_) then skip
      []   pcall(D1) then local D2 D3 in {SubInProg now S D1 D2}
                   {Proc D2 D3} {Final D3 S} end
      else fail
      end
  end

  proc {Trans D S Dp Sp}
      case D of nil then fail
      []   test(Cond) then {Holds.yes Cond S} Sp=S Dp=nil
      []   seq(D1 D2) then choice D1r in {Trans D1 S D1r Sp} Dp=seq(D1r D2)
                           []     {Final D1 S} {Trans D2 S Dp Sp}
                           end
      []   pick(D1 D2) then choice {Trans D1 S Dp Sp}
                            [] {Trans D2 S Dp Sp}
                            end
      []   pi(V D1) then local D2 in {SubInProg V _ D1 D2}
                                     {Trans D2 S Dp Sp} end
      []   star(D1) then local D2 in {Trans D S D2 Sp} Dp=seq(D2 star(D1)) end
      []   ifte(Cond D1 D2) then choice {Holds.yes Cond S}
                                        {Trans D1 S Dp Sp}
                                 []     {Holds.no Cond S}
                                        {Trans D2 S Dp Sp}
                                 end
      []   wloop(Cond D1) then local D2 in {Holds.yes Cond S} {Trans D1 S D2 Sp}
                               Dp=seq(D2 wloop(Cond D1)) end
      []   conc(D1 D2) then choice D1r D2r C1 C2 CT T in
                                       {Step D1 S D1r res(C1 T S)}
                                       {Step D2 S D2r res(C2 T S)}
                                       {NegAsFail proc {$} A in
                                                      {IsMember A C1}
                                                      {IsMember A C2}
                                                      {GetActor A _}
                                                  end}
                                       {Union C1 C2 CT} {Poss CT T S}
                                       Sp=res(CT T S) Dp=conc(D1r D2r)
                            []     D1r in {Trans D1 S D1r Sp} Dp=conc(D1r D2)
                            []     D2r in {Trans D2 S D2r Sp} Dp=conc(D1 D2r)
                            end
      []   pconc(D1 D2) then choice D1r in {Trans D1 S D1r Sp} Dp=pconc(D1r D2)
                             []     D2r in {Trans D2 S D2r Sp} Dp=pconc(D1 D2r)
                                    {NegAsFail proc {$} {Trans D1 S _ _} end}
                             end
      []   cstar(D1) then local D2 in {Trans D1 S D2 Sp}
                          Dp=conc(D2 cstar(D1)) end
      []   pcall(D1) then local Body D2 in
                          {SubInProg now S D1 D2} {Proc D2 Body}
                          {Trans Body S Dp Sp} end
      else local D1 D2 T in
              {ToCAct D D1} {SubInProg now S D1 D2}
              {RI.lessEq {ToRIVar {SitStart S}} T}
              choice LntpS in {LNTP S LntpS}
                     choice %% Can do before LNTP actions
                            {RI.greaterEq T {ToRIVar {SitStart S}}}
                            {RI.less T {ToRIVar LntpS}} {Poss D2 T S}
                            Sp=res(D2 T S) Dp=nil
                     []     FindNAct NActs in
                                       FindNAct = proc {$ A}
                                         {IsNatural A} {Poss A LntpS S}
                                       end
                            NActs={Search.base.all FindNAct} (NActs\=nil)=true
                            choice %% Can do with LNTP actions
                                   CANat in CANat={Union D2 NActs}
                                   {Poss CANat LntpS S}
                                   Sp=res(CANat LntpS S) Dp=nil
                            []     %% Can do LNTP actions first
                                   {Poss NActs LntpS S}
                                   Sp=res(NActs LntpS S) Dp=D
                            end
                     end
              []     {NegAsFail proc {$} {LNTP S _} end}
                     {Poss D2 T S} Sp=res(D2 T S) Dp=nil
                          
              end
           end
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
    local Dp in
      {TransStar D S Dp Sp}
      {Final Dp Sp}
    end
  end

  proc {Proc D2 B}
    fail
  end

  proc {SubInProg Term Value D1 D2}
    if {IsFree D1} then
      D2=D1
    else
      if D1==Term then
        D2=Value
      else
        if {IsRecord D1} then
          {SubInProg_Record Term Value D1 D2}
        else
          D2=D1
        end
      end
    end
  end

  proc {SubInProg_Record Term Value R1 R2}
    Fields={Arity R1}
  in
    {Record.clone R1 R2}
    {ForAll Fields proc {$ F}
                     R2.F={SubInProg Term Value R1.F}
                   end}
  end

  proc {Union L1 L2 LF}
    case L1 of nil then LF=L2
    []   H|T then local LI in LI={Union T L2}
                  if {Member H LI} then
                    LF=LI
                  else
                    LF=H|LI
                  end
                 end
    end
  end

  proc {IsAgent Agt}
    choice  Agt=thomas
    []      Agt=richard
    []      Agt=harriet
    end
  end

  proc {IsTask Tsk}
    choice Cont in Tsk=mix(Cont _) {ObjIsType Cont container}
    []     Cont in Tsk=chop(Cont) {ObjIsType Cont container}
    end
  end

  proc {IsPrimObjT Obj Type}
    choice Type=knife {IsMember Obj [knife1 knife2 knife3]}
    []     Type=bowl {IsMember Obj [bowl1 bowl2 bowl3]}
    []     Type=board {IsMember Obj [board1 board2]}
    []     Type=oven {IsMember Obj [oven1]}
    []     Type=flour {IsMember Obj [flour1 flour2 flour3 flour4 flour5]}
    []     Type=sugar {IsMember Obj [sugar1 sugar2 sugar3 sugar4 sugar5]}
    []     Type=egg {IsMember Obj [egg1 egg2 egg3]}
    []     Type=tomato {IsMember Obj [tomato1 tomato2]}
    []     Type=lettuce {IsMember Obj [lettuce1]}
    []     Type=carrot {IsMember Obj [carrot1 carrot2 carrot3]}
    end
  end

  proc {IsPrimObj Obj}
    {IsPrimObjT Obj _}
  end

  proc {IsSuperType Type SType}
    choice SType=container {IsMember Type [bowl board oven]}
    []     SType=ingredient
           {IsMember Type [flour egg sugar tomato lettuce carrot]}
    end
  end

  proc {ObjIsType Obj Type}
    choice  {IsPrimObjT Obj Type}
    []      SubType in {IsSuperType SubType Type} {ObjIsType Obj SubType}
    end
  end

  proc {IsPrimAction Act}
    choice Agt Obj in Act=acquire_object(Agt Obj)
                      {IsAgent Agt}  {IsPrimObj Obj}
    []     Agt Obj in Act=release_object(Agt Obj)
                      {IsAgent Agt}  {IsPrimObj Obj}
    []     Agt in Act=set_timer(Agt _ _) {IsAgent Agt}
    []     Act=ring_timer(_)
    []     Agt Conts Dest in Act=place_in(Agt Conts Dest)
                             {IsAgent Agt} {IsPrimObj Conts}
                             {ObjIsType Dest container}
    []     Agt Source Dest in Act=transfer(Agt Source Dest)
                              {IsAgent Agt} {ObjIsType Source container}
                              {ObjIsType Dest container}
    []     Agt Tsk in Act=begin_task(Agt Tsk)
                       {IsAgent Agt} {IsTask Tsk}
    []     Agt Tsk in Act=end_task(Agt Tsk)
                       {IsAgent Agt} {IsTask Tsk}
    end
  end

  proc {IsNatural Act}
    choice Act=ring_timer(_)
    []     Act=end_task(_ _)
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

  proc {Script Root}
    {Do acquire_object(thomas knife1) res([set_timer(richard t1 10)] 0 s0) Root}
  end

end

in 

local E Ans in

  {Browse Ans}
  E={New Search.parallel init(localhost)}
  Ans={E one(Goloz $)}

end
