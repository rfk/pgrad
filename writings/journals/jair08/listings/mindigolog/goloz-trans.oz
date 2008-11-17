proc {Trans D S Dp Sp}
  case D of nil then fail
  []   test(Cond) then choice {Sitcalc.holds Cond S}
                              Sp=S Dp=nil
                       []     Tn = {Sitcalc.lntp S}
                              Cn = {Sitcalc.pna S} in
                              Dp=D Sp=res(Cn Tn S)
                       end
  []   seq(D1 D2) then choice D1r in {Trans D1 S D1r Sp}
                                     Dp=seq(D1r D2)
                       []            {Final D1 S}
                                     {Trans D2 S Dp Sp}
                       end
  []   choose(D1 D2) then choice {Trans D1 S Dp Sp}
                          []     {Trans D2 S Dp Sp}
                          end
  [] ... <additional cases ommitted> ...
  end
end
