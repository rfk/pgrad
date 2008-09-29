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

    Search

export

    Trans
    Final
    Step
    TransStar
    Do
    ParallelDo

define

  %  {Trans D S Dp Sp}  -  MIndiGolog transition semantics
  %
  proc {Trans D S Dp Sp}
      case D of nil then fail
      []   test(Cond) then choice {Sitcalc.holds Cond S} Sp=S Dp=nil
                           []     Tn = {Sitcalc.lntp S}
                                  Cn = {Sitcalc.pna S} in
                                  Dp=D Sp=res(Cn Tn S)
                           end
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
      []   pcall(D1) then Body in
                          {Procedures.procdef D1 Body}
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
                             {Control.log planning}
                             try
                               {ParallelDo D1 S Sr}
                               %[Sr] = {Search.base.one proc {$ Sr}
                               %  {Do D1 {LP.copyTerm S} Sr}
                               %end}
                               Dr = dosteps({Sitcalc.toStepsList S Sr})
                               {Control.sendMessage Dr}
                               {Trans Dr S Dp Sp}
                             catch _ then
                               {Control.log plan_failed}
                               {Control.sendMessage plan_failed}
                               fail
                             end
                           else
                             {Control.log waiting_for_plan}
                             {Control.waitForMessage Dr}
                             if Dr == plan_failed then
                               {Control.log plan_failed}
                               fail
                             end
                             {Trans Dr S Dp Sp}
                           end
      []   dosteps(Steps) then C T Steps2 in
                               Steps = (C#T)|Steps2
                               Sp = res(C T S)
                               Dp = dosteps(Steps2)
      else C T in
           {Time.decl T}
           {Sitcalc.toConcAct D C}
           choice Tn={Sitcalc.lntp S}
                  Cn={Sitcalc.pna S}
                in
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

  %  {Final D S}  -  termination semantics for MIndiGolog
  %
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
      []   pcall(D1) then local Body in
                            {Procedures.procdef D1 Body}
                            {Final Body S}
                          end
      []   search(D1) then {Final D1 S}
      []   dosteps(Steps) then Steps = nil
      else fail
      end
  end

  %  Find a sequence of transitions from (D,S) to (Dp,Sp)
  %
  proc {TransStar D S Dp Sp}
    choice  Dp=D Sp=S
    []      Dr Sr in {Trans D S Dr Sr} {TransStar Dr Sr Dp Sp}
    end
  end

  %  Find a sequence of transitions from (D,S) to (Dp,res(C T S)).
  %  In other words, find an actual action to perform as the next step.
  %
  proc {Step D S Dp Sp}
    choice Sp=res(_ _ S) {Trans D S Dp Sp}
    []     Dr in {Trans D S Dr S} {Step Dr S Dp Sp}
    end
  end

  %  {Do D S Sp}  -  execution semantics for MIndiGolog.
  %  Find a sequence of transitions beginning from (D,S), and ending in
  %  a terminating state with situation Sp.
  %
  proc {Do D S Sp}
     Dp
  in
     {TransStar D S Dp Sp}
     {Final Dp Sp}
  end
  
  %  {ParallelDo D S Sp}  -  distributed execution planning for MIndiGolog
  %
  %  This procedure mirrors {Doi D S Sp}, but uses Mozart's ParallelSearch
  %  feature to distributed the planning workload across the whole team.
  %  Since it may be called from within a computation space, we need the
  %  implementation to run in a top-level thread and we call into it by
  %  communicating on a Port.
  %
  proc {IParallelDo D S Sp}
    PDo PSearch Ds Ss Machines Soln
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
    Machines = {Record.make init Control.subordinates}
    for Agt in {Record.arity Machines} do
      Machines.Agt = 1#ssh
    end
    {Control.log parallel_search_using(Machines)}
    PSearch = {New Search.parallel Machines}
    Soln = {PSearch one(PDo $)}
    if Soln == nil then Sp = nil
    else [(D#S#Sp)] = {LP.unserialize Soln} end
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
      if Sps == nil then fail end
      Sp = {LP.unserialize Sps}
    end
  end

end
