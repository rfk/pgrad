%
%  Execution.oz
%
%  Implements an execution, a prime event structure where each event is
%  a step of execution of the program, and that satisfies some additional
%  constraints.
%
%  Each event in the execution is uniquely identified by an integer,
%  which is its order of insertion into the execution.
%


functor

import

  LP at '../Utils/LP.ozf'
  MList at '../Utils/MList.ozf'
  SitCalc

export

  Init
  Insert
  Finish

  Enablers
  Alternatives
  Preceeds
  Conflicting
  Distinguishable
  Branches
  ToSituation

  getAction
  getObs

  Holds
  HoldsFOF
  HoldsW

define

  %
  %  Initialize a new (empty) execution.
  %  Its history and future are both initially empty.
  %
  proc {Init Ex}
    Ex = ex(count: 0
            enablers: e()
            alternatives: a() 
            distinguishable: d()
           )
  end

  %
  %  List the events that enable the given event N.
  %
  proc {Enablers Ex N Ns}
    Ns = Ex.enablers.N
  end

  %
  %  List the events that could occur instead of the given event N.
  %
  proc {Alternatives Ex N Ns}
    Ns = Ex.alternatives.N
  end

  %
  %  Determine whether event N1 is required to happen before event N2.
  %
  proc {Preceeds Ex N1 N2 B}
    if {List.member N1 Ex.enablers.N2} then
      B = true
    else
      B = for return:R default:false Ne in Ex.enablers.N2 do
            if {Preceeds Ex N1 Ne} then {R true} end
          end
    end
  end

  %
  %  Determine whether events N1 and N2 are in conflict, i.e. they
  %  cannot appear together in a run.
  %
  proc {Conflicting Ex N1 N2 B}
    if {List.member N2 Ex.alternatives.N1} then
      B = true
    else
      B = for return:R default:false Na in Ex.alternatives.N1 do
            if {Preceeds Ex Na N2} then {R true} end
          end
    end
  end

  %
  %  Determine whether events N1 and N2 are distinguishable from
  %  the perspective of agent A.  This is true if and only if
  %  every run up to N1 produces a different observation history
  %  for A than every run up to N2.
  %
  proc {Distinguishable Ex A N1 N2 B}
    B = Ex.distinguishable.N1.N2.A
  end

  %
  %  Return the canonical situation term representing the given
  %  branch of the execution.
  %
  proc {ToSituation Ex Br S}
    % TODO: Exec.toSituation
    S = s0
  end

  %
  %  Insert a new step into the execution.  Returns a list
  %  of event IDs representing the possible outcomes of performing
  %  that step.  These events are {Alternatives} to each other.
  %
  proc {Insert ExIn Step ExOut Outcomes}
    ExOut = ExIn
    Outcomes = nil
  end

  %
  %  Determine whether step S can be ensured to happen after event N.
  %  
  proc {Orderable Ex N S B}
    B = false
  end

  proc {Enables Ex N1 N2 B}
    if {Orderable Ex N1 N2} then
      if {Ordered Ex N1 N2} then 
        B = true
      else
        choice B=true [] B=false end
      end
    elseif {Ordered Ex N1 N2} then
      fail
    else
      B = false
    end
  end

  proc {OutcomesAA E Act Agt Outcomes}
    CanObs = {HoldsW E canObs(Agt Act)}
  in
    if CanObs == no then
      Outcomes = [E]
    else
      Acc = {LP.listAcc Outcomes}
      CanSense = {HoldsW E canSense(Agt Act)} 
     in
      if CanObs == unknown then
        {Acc E}
      end
      if CanSense \= yes then
        {Acc {Addobs E o(Agt: [Act])}}
      end
      if CanSense \= no then
        AOuts = {SitCalc.actionOutcomes Act} in
        if AOuts == nil then
          {Acc {Addobs E o(Agt: [Act])}}
        else 
          for Res#Cond in AOuts do
            _={LP.ifNot proc {$ R}
                           {Holds E neg(Cond)}
                        end
                        proc {$ R}
                           {Acc {Addobs E o(Agt: [Act#Res])}}
                        end}
          end
        end
      end
      {Acc nil}
    end
  end

  %
  %  Determine whether F is known to hold after the execution of E.
  %  The definition of 'known' can be any knowledge operator for
  %  which we have an implementation, and which is equivalent across
  %  agents (e.g: dknows, sknows, cknows)
  %
  %  Note that since this is based on knowledge, there's no excluded
  %  middle - it's possible for holds(F E) and holds(neg(F) E) to both
  %  be false.
  %
  %  Designed to be used during program search, so it's an assertion
  %  rather than a function, and will bind variables in F to ensure that
  %  it holds.
  %
  proc {Holds E F}
    Fml Binder Binding
  in
    Fml = {SitCalc.fof.parseRecord F Binder}
    Binding = {HoldsFOF E Fml}
    {Binder Binding}
  end

  proc {HoldsFOF E FmlIn Bind}
    Fml = {SitCalc.uniformize FmlIn}
  in
    case E of ex(Step E2) then
     if {SitCalc.fof.contradiction {SitCalc.fof.impl SitCalc.axioms Fml}} then
       fail
     else FmlR in
       %TODO: include observations in regression for holdsFOF
       FmlR = {SitCalc.regress Fml Step.action}
       {HoldsFOF E2 FmlR Bind}
     end
    else
      Axioms = {SitCalc.fof.conj SitCalc.axioms SitCalc.initially} in
      {SitCalc.fof.prove {SitCalc.fof.impl Axioms Fml} Bind}
    end
  end

  %
  %  Determine if it is known whether F holds after the execution of E.
  %  Unlike {Holds}, this procedure returns one of 'yes', 'no' or 
  %  'unknown' and will not bind free variables.
  %
  proc {HoldsW E F Res}
    Fml = {SitCalc.fof.parseRecord F _}
  in
    Res = {HoldsW_FOF E Fml}
  end

  proc {HoldsW_FOF E FIn Res}
    F = {SitCalc.uniformize FIn}
    Res2
  in
    case E of ex(Step E2) then
      Res2 = {SitCalc.fof.tautOrCont {SitCalc.fof.impl SitCalc.axioms F}}
      if Res2 == taut then Res = yes
      elseif Res2 == cont then Res = no
      else FmlR in
        %TODO: include observations in regression for HoldsW_FOF
        FmlR = {SitCalc.regress F Step.action}
        {HoldsW_FOF E2 FmlR Res}
      end
    else
      Axioms = {SitCalc.fof.conj SitCalc.initially SitCalc.axioms} in
      Res2 = {SitCalc.fof.tautOrCont {SitCalc.fof.impl Axioms F}}
      if Res2 == taut then Res = yes
      elseif Res2 == cont then Res = no
      else Res = unknown end
    end
  end

end
