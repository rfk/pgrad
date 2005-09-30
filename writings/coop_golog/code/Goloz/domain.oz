
declare

  proc {IsMember Elem List}
    choice List=nil fail
    []     List=Elem|_
    []     NewList Head in List=Head|NewList {IsMember Elem NewList}
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
           {PreceedsEq S1 Sp} ({SitStart Sp}=<T)=true
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
    local A Others in
      {IsNatural A} {Poss A T S} ({SitStart S}=<T)=true
      Others=proc{$}
               local A2 T2 in
                 {IsNatural A2}
                 {Poss A2 T2 S}
                 (T2<T)=true
               end
             end
      {NegAsFail Others}
    end
  end

  proc {ToCAct A C}
    if A==_|_ then
        C=A
    else
        C=[A]
    end
  end

  proc {Final D S}
    local D1 D2 in
      choice D=nil
      []     D=seq(D1 D2) {Final D1 S} {Final D2 S}
      []     D=pick(D1 D2) choice {Final D1 S} [] {Final D2 S} end
      []     V in D=pi(V D1) {SubInProg V _ D1 D2} {Final D2 S}
      []     D=start(_)
      []     Cond in D=ifte(Cond D1 D2)
                     choice {Holds.yes Cond S} {Final D1 S}
                     []     {Holds.no Cond S} {Final D2 S}
                     end
      []     Cond in D=wloop(Cond D1)
                     choice {Holds.no Cond S}
                     []     {Final D1 S}
                     end
      []     D=conc(D1 D2) {Final D1 S} {Final D2 S}
      []     D=pconc(D1 D2) {Final D1 S} {Final D2 S}
      []     D=cstar(_)
      []     D3 in D=pcall(D1) {SubInProg now S D1 D2}
                   {Proc D2 D3} {Final D3 S}
      end
    end
  end

  proc {Trans D S Dp Sp}
    local D1 D2 in
      choice  D=nil fail
      []      {ToCAct D D1} {SubInProg now S D1 D2}
              choice T LntpS in {LNTP S LntpS}
                                /* TODO: during and after LNTP */
                                (T>{SitStart S})=true
                                (T<LntpS)=true {Poss D2 T S}
                                Sp=res(D2 T S) Dp=nil
              []     T in {Poss D2 T S} (T>={SitStart S})=true
                          Sp=res(D2 T S) Dp=nil
              end
      []      Cond in D=test(Cond) {Holds.yes Cond S} Sp=S Dp=nil
      []      D=seq(D1 D2) choice D1r in {Trans D1 S D1r Sp} Dp=seq(D1r D2)
                           []     {Final D1 S} {Trans D1 S Dp Sp}
                           end
      []      D=pick(D1 D2) choice {Trans D1 S Dp Sp}
                              [] {Trans D2 S Dp Sp}
                              end
      []      V in D=pi(V D1) {SubInProg V _ D1 D2} {Trans D2 S Dp Sp}
      []      D=start(D1) {Trans D S D2 Sp} Dp=seq(D2 star(D1))
      []      Cond in D=ifte(Cond D1 D2) choice {Holds.yes Cond S}
                                                {Trans D1 S Dp Sp}
                                         []     {Holds.no Cond S}
                                                {Trans D2 S Dp Sp}
                                         end
      []      Cond in D=wloop(Cond D1) {Holds.yes Cond S} {Trans D1 S D2 Sp}
                      Dp=seq(D2 wloop(Cond D1))
      []      D=conc(D1 D2) choice D1r in {Trans D1 S D1r Sp} Dp=conc(D1r D2)
                            []     D2r in {Trans D2 S D2r Sp} Dp=conc(D1 D2r)
                            /* TODO: concurrent stepping of both */
                            end
      []      D=pconc(D1 D2) choice D1r in {Trans D1 S D1r Sp} Dp=pconc(D1r D2)
                             []     D2r in {Trans D2 S D2r Sp} Dp=pconc(D1 D2r)
                                    {NegAsFail proc {$} {Trans D1 S _ _} end}
                             end
      []      D=cstar(D1) {Trans D1 S D2 Sp} Dp=conc(D2 cstar(D1))
      []      Body in D=pcall(D1) {SubInProg now S D1 D2} {Proc D2 Body}
                      {Trans Body S Dp Sp}
      end
    end
  end

  proc {Proc D2 B}
    fail
  end

  proc {SubInProg Term Value D1 D2}
    D1=D2
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
    choice Agt Obj in A=acquire_object(Agt Obj)
                      {Holds.no has_object(_ Obj) S}
                      {Holds.no doing_task(Agt _ _) S}
                      {Holds.no used(Obj) S}
    []     Agt Obj in A=release_object(Agt Obj)
                      {Holds.yes has_object(Agt Obj) S}
                      {Holds.no doing_task(Agt _ _) S}
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
                      {NegAsFail proc {$} {FProc.minus F S} end }
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

      plus: proc{$ timer_set(ID Dur) S}
              local C T Sp in
                S=res(C T Sp)
                choice {IsMember set_timer(_ ID Dur) C}
                []     OldDur in {Holds.yes timer_set(ID OldDur) Sp}
                       Dur=OldDur-(T-{SitStart Sp})
                       {NegAsFail proc {$} {IsMember ring_timer(ID) C} end}
                end
              end
            end

      minus: proc{$ timer_set(ID Dur) S}
               local C in 
                 S=res(C _ _)
                 {IsMember ring_timer(ID) C}
               end
             end

      init: proc{$ F} fail end
    )
  )

in
  local Control Dp Sp Ans in 

    Control=seq(acquire_object(thomas egg1) acquire_object(thomas bowl1))
    {Search.base.one {proc {$ E} {Holds.yes has_object(thomas egg1) s0} end} Ans}
    {Browse Ans}

  end
  


