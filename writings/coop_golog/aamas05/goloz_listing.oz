
proc {Final D S}
  case D of nil then skip
  []   seq(D1 D2) then {Final D1 S} {Final D2 S}
  []   pick(D1 D2) then choice {Final D1 S}
                        [] {Final D2 S}
                        end
  []   ifte(Cond D1 D2) then
           choice {Holds.yes Cond S} {Final D1 S}
           []     {Holds.no Cond S} {Final D2 S}
           end
  []   ... <additional cases ommitted> ...
  []   conc(D1 D2) then {Final D1 S} {Final D2 S}
  else fail
  end
end

proc {Trans D S Dp Sp}
  case D of nil then fail
  []   seq(D1 D2) then choice D1r in
                              {Trans D1 S D1r Sp}
                              Dp=seq(D1r D2)
                       []     {Final D1 S}
                              {Trans D2 S Dp Sp}
                       end
  []   ... <additional cases ommitted> ...
  []   conc(D1 D2) then
                   choice D1r D2r C1 C2 CT T in
                       {Step D1 S D1r res(C1 T S)}
                       {Step D2 S D2r res(C2 T S)}
                       {NegAsFail proc {$} A in
                                  {IsMember A C1}
                                  {IsMember A C2}
                                  {GetActor A _}
                                  end}
                       {Union C1 C2 CT}
                       {Poss CT T S} Sp=res(CT T S)
                       Dp=conc(D1r D2r)
                   []  D1r in {Trans D1 S D1r Sp}
                              Dp=conc(D1r D2)
                   []  D2r in {Trans D2 S D2r Sp}
                              Dp=conc(D1 D2r)
                   end
  []   ... <additional cases ommitted> ...
  else local D1 D2 T in
    {ToCAct D D1} {SubInProg now S D1 D2}
    {RI.lessEq {ToRIVar {SitStart S}} T}
    choice LntpS in {LNTP S LntpS}
       choice %% Can do before LNTP actions
          {RI.greaterEq T {ToRIVar {SitStart S}}}
          {RI.less T {ToRIVar LntpS}} {Poss D2 T S}
          Sp=res(D2 T S) Dp=nil
       [] FindNAct NActs in
            FindNAct = proc {$ A}
                   {IsNatural A} {Poss A LntpS S}
                       end
            NActs={Search.base.all FindNAct}
            (NActs\=nil)=true
            choice %% Can do with LNTP actions
               CANat in CANat={Union D2 NActs}
               {Poss CANat LntpS S}
               Sp=res(CANat LntpS S) Dp=nil
            [] %% Can do LNTP actions first
               {Poss NActs LntpS S}
               Sp=res(NActs LntpS S) Dp=D
            end
       end
    [] {NegAsFail proc {$} {LNTP S _} end}
       {Poss D2 T S} Sp=res(D2 T S) Dp=nil
    end
   end
  end
end

proc {TransStar D S Dp Sp}
  choice  Dp=D Sp=S
  []      Dr Sr in {Trans D S Dr Sr}
          {TransStar Dr Sr Dp Sp}
  end
end

proc {Step D S Dp Sp}
  choice Sp=res(_ _ S) {Trans D S Dp Sp}
  []   Dr in {Trans D S Dr S} {Step Dr S Dp Sp}
  end
end

proc {Do D S Sp}
  local Dp in
    {TransStar D S Dp Sp}
    {Final Dp Sp}
  end
end
