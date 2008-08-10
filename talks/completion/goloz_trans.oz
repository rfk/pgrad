proc {Trans D S Dp Sp}
  case D of nil then fail
  [] test(C) then {Holds.yes C S} Sp=S Dp=nil
  [] pick(D1 D2) then choice
                         {Trans D1 S Dp Sp}
                     []  {Trans D2 S Dp Sp}
                     end
  [] ... <additional cases ommitted> ...
  end
end
