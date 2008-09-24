
functor

import

  MIndiGolog
  Time
  Sitcalc
  Domain

  Application
  Property
  System
  Search

define

  {Property.put 'print.width' 1000}
  {Property.put 'print.depth' 1000}
  {Property.put 'errors.width' 1000}
  {Property.put 'errors.depth' 1000}

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
  %Holds = {Search.base.one proc{$ R} T in
  %  {Sitcalc.holds hasObject(jim bowl1) res([acquire(jim bowl1)] 1 s0)}
  %  R = unit
  %end}
  %{System.show Holds}

  {Application.exit 0}

end
