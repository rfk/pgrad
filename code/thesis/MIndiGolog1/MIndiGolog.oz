%
%  MIndiGolog.oz:  semantics of MIndiGolog
%

functor

import

    Sitcalc at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Sitcalc.ozf'
    LP at '/storage/uni/pgrad/code/thesis/MIndiGolog1/LP.ozf'
    Domain at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Domain.ozf'
    Procedures at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Procedures.ozf'
    Time at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Time.ozf'
    Control at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Control.ozf'

    System
    Search
    Module

export

    Trans
    Final
    Do
    Step
    TransStar

define

  proc {Trans D S Dp Sp}
      case D of nil then fail
      []   test(Cond) then {Sitcalc.holds Cond S} Sp=S Dp=nil
                           % TODO: reinstate this case
                           %   {Sitcalc.lntp S Tn}
                           %   {Sitcalc.pna S Cn}
                           %   Dp=D Sp=res(Cn Tn S)
      []   seq(D1 D2) then choice D1r in {Trans D1 S D1r Sp} Dp=seq(D1r D2)
                           []            {Final D1 S} {Trans D2 S Dp Sp}
                           end
      []   choose(D1 D2) then choice {Trans D1 S Dp Sp}
                            []       {Trans D2 S Dp Sp}
                            end
      []   pick(V D1) then D2 in
                           {LP.subInTerm V _ D1 D2}
                           {Step D2 S Dp Sp}
      []   star(D1) then D2 in
                         {Trans D S D2 Sp}
                         Dp=seq(D2 star(D1))
      []   ifte(Cond D1 D2) then choice {Sitcalc.holds Cond S}
                                        {Trans D1 S Dp Sp}
                                 []     {Sitcalc.holds neg(Cond) S}
                                        {Trans D2 S Dp Sp}
                                 end
      []   wloop(Cond D1) then D2 in
                             {Sitcalc.holds Cond S}
                             {Trans D1 S D2 Sp}
                             Dp=seq(D2 wloop(Cond D1))
      []   conc(D1 D2) then choice D1r D2r C1 C2 Cu T in
                                     {Step D1 S D1r res(C1 T S)}
                                     {Step D2 S D2r res(C2 T S)}
                                     {LP.neg proc {$} A in
                                        {LP.member A C1}
                                        {LP.member A C2}
                                        {LP.neg proc {$} {Domain.isExog A} end}
                                     end}
                                     {LP.union C1 C2 Cu}
                                     {Sitcalc.legal Cu T S}
                                     Sp=res(Cu T S) Dp=conc(D1r D2r)
                            []     D1r in {Trans D1 S D1r Sp} Dp=conc(D1r D2)
                            []     D2r in {Trans D2 S D2r Sp} Dp=conc(D1 D2r)
                            end
      []   pconc(D1 D2) then choice D1r in {Trans D1 S D1r Sp} Dp=pconc(D1r D2)
                             []     D2r in {Trans D2 S D2r Sp} Dp=pconc(D1 D2r)
                                    {LP.neg proc {$}
                                        {Trans D1 {LP.copyTerm S} _ _}
                                    end}
                             end
      []   cstar(D1) then D2 in
                          {Trans D1 S D2 Sp}
                          Dp=conc(D2 cstar(D1))
      []   pcall(D1) then Body D2 in
                          {LP.subInTerm now S D1 D2}
                          {Procedures.procdef D2 Body}
                          {Trans Body S Dp Sp}
      []   search(D1) then Sr Dr in
                           % Old, non-parallel-search way:
                           %
                           %  {Trans D1 S Dr Sp}
                           %  {Do Dr Sp Sr}
                           %  Dp = dosteps({Sitcalc.toStepsList Sp Sr})
                           %
                           % New, parallel-search way
                           %
                           if Control.teamMember == Control.teamLeader then
                             {System.show planning}
                             {Trans D1 S Dr Sp}
                             {ParallelDo Dr Sp Sr}
                             Dp = dosteps({Sitcalc.toStepsList Sp Sr})
                             {Control.sendMessage Dp#Sp}
                           else Msg in
                             {System.show waiting_for_plan}
                             {Control.waitForMessage Msg}
                             (Dp#Sp) = Msg
                           end
      []   dosteps(Steps) then C T Steps2 in
                               Steps = (C#T)|Steps2
                               Sp = res(C T S)
                               Dp = dosteps(Steps2)
      else D1 C T in
           {Time.decl T}
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
                  []     %% Can do LNTP actions first
                         Sp=res(Cn Tn S) Dp=D
                  []     %% Can with with LNTP actions
                         Cu={LP.union C Cn} in
                         {Sitcalc.legal Cu Tn S}
                         Sp=res(Cu Tn S) Dp=nil
                  end
           []     {LP.neg proc {$}
                    {Sitcalc.lntp {LP.copyTerm S} _}
                  end}
                  {Sitcalc.legal C T S}
                  Sp=res(C T S) Dp=nil
           end
      end
  end

  proc {Final D S}
      case D of nil then skip
      []   seq(D1 D2) then {Final D1 S} {Final D2 S}
      []   test(Cond) then {Sitcalc.holds Cond S}
      []   choose(D1 D2) then choice {Final D1 S} [] {Final D2 S} end
      []   pick(V D1) then local D2 in {LP.subInTerm V _ D1 D2} {Final D2 S} end
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
                            {Procedures.procdef D2 D3}
                            {Final D3 S}
                          end
      []   search(D1) then {Final D1 S}
      []   dosteps(Steps) then Steps = nil
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
  
  proc {IParallelDo D S Sp}
    PDo PSearch Ds Ss Machines
  in
    Ds = {LP.serialize D}
    Ss = {LP.serialize S}
    functor PDo
      import
        MG at '/storage/uni/pgrad/code/thesis/MIndiGolog1/MIndiGolog.ozf'
        LP at '/storage/uni/pgrad/code/thesis/MIndiGolog1/LP.ozf'
      export
        Script
    define
        proc {Script R}
          Dl Sl Spl
        in
          {LP.unserialize Ds Dl}
          {LP.unserialize Ss Sl}
          {MG.'do' Dl Sl Spl}
          R = {LP.serialize (Dl#Sl#Spl)}
        end
    end
    %Machines = {Record.make init Control.agents}
    Machines = {Record.make init Control.subordinates}
    for Agt in {Record.arity Machines} do
      Machines.Agt = 1#ssh
    end
    {System.show parallel_search_using(Machines)}
    PSearch = {New Search.parallel Machines}
    [(D#S#Sp)] = {LP.unserialize {PSearch one(PDo $)}}
  end

  ParallelDo = _
  local
    IPort IStream
  in
    IPort = {Port.new IStream}
    thread
      for (Ds#Ss)#Sps in IStream do D S Sp in
        {LP.unserialize (Ds#Ss) (D#S)}
        {IParallelDo D S Sp}
        {LP.serialize Sp Sps}
      end
    end
    proc {ParallelDo D S Sp} Sps in
      Sps = !!{Port.sendRecv IPort {LP.serialize (D#S)}}
      {Value.wait Sps}
      Sp = {LP.unserialize Sps}
      {System.show done}
    end
  end

end
