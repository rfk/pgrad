proc {IsFinal D S B} F in
  F = {Search.base.one proc {$ R}
          {MIndiGolog.final D S}
          R=unit
      end}
  if F == nil then B=false
  else B=true end
end

proc {NextStep D S Dp Sp}
  [Dp#Sp] = {Search.base.one proc {$ R} DpR SpR in
                {MIndiGolog.step D S DpR SpR}
                R = DpR#SpR
            end}
end

proc {Run D S}
  if {IsFinal D S} then
    {Control.log succeeded}
  else Dp Sp C T in
      try
        {NextStep D S Dp Sp}
        Sp = res(C T S)
        T = {Time.min T}
        {Control.execute C T}
        {Run Dp Sp}
      catch _ then
        {Control.log failed}
      end
  end
end

{Run pcall(main) s0}
