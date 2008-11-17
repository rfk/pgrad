proc {IsFinal D S B} F in
  F = {Search.base.one proc {$ R}
          {MIndiGolog.final D S} R=unit
      end}
  if F == nil then B=false else B=true end
end

proc {NextStep D S Dp Sp}
  [Dp#Sp] = {Search.base.one proc {$ R} DpR SpR in
                {MIndiGolog.step D S DpR SpR}
                R = DpR#SpR
            end}
end
