
functor

import

  MIndiGolog
  Time
  Sitcalc
  Domain
  LP
  Control

  Application
  System
  Search
  Property
  Explorer

define

  {Property.put 'print.width' 1000}
  {Property.put 'print.depth' 1000}
  {Property.put 'errors.width' 1000}
  {Property.put 'errors.depth' 1000}

  MyArgs = {Application.getArgs plain}
  Control.teamMember = {String.toAtom MyArgs.1}
  Control.teamLeader = jon
  {Control.init}

  % Search to determine whether current state is final
  proc {IsFinal D S B} F in
    F = {Search.base.one proc {$ R} {MIndiGolog.final D S} R=unit end}
    if F == nil then B=false
    else B=true end
  end

  % Search to determine next step for the current state
  proc {NextStep D S Dp Sp}
    [Dp#Sp] = {Search.base.one proc {$ R} DpR SpR in
                {MIndiGolog.step D S DpR SpR}
                R = DpR#SpR
              end}
  end


  % Recursive loop, executing one step at a time
  proc {Run D S}
    if {IsFinal D S} then
      {System.show succeeded}
    else Dp Sp C T in
        try
          {NextStep D S Dp Sp}
          Sp = res(C T S)
          T = {Time.min T}
          {System.show execute(C T)}
          {Run Dp Sp}
        catch _ then
          {System.show failed}
        end
    end
  end

  {System.show start}
  {Run pcall(main) s0}

  %proc {Tester R} T1 T2 T3 T4 T5 S F in
  %  {Time.decl T1} {Time.decl T2} {Time.decl T3} {Time.decl T4} {Time.decl T5}
  %  {Time.less T1 T2}
  %  S = res([placeIn(jim carrot1 bowl2)] T5 res([transfer(joe board1 bowl1)] T4 res([placeIn(joe tomato1 board1)] T3 res([acquire(joe tomato1)] T2 res([acquire(joe board1)] T1 s0)))))
  %  F = contents(_ _)
  %  {Sitcalc.holds F S}
  %  {System.show F}
  %  R = unit
  %end
  %{System.show {Search.base.all Tester}}

  {Application.exit 0}

end
