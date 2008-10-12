  proc {Trans D H Dp Sp}
    case D of 
        nil then fail
    []  test(Cond) then
          {Sitcalc.holds Cond H}
          Dp = nil
          Sp = {Step.init step(test:Cond)}
    []  choose(D1 D2) then
          choice {Trans D1 H Dp Sp}
          []  {Trans D2 H Dp Sp}
          end
    []  conc(D1 D2) then
          choice D1p S1p in
              {Trans D1 H D1p S1p}
              Dp = conc(D1p D2)
              Sp = {Step.addthred S1p l}
          []  D2p S2p in
              {Trans D2 H D2p S2p}
              Dp = conc(D1 D2p)
              Sp = {Step.addthred S2p r}
          end
    [] ... <additional cases ommitted> ...
    else  Dp = nil
          {Sitcalc.legal [D] H}
          Sp = {Step.init step(action:D)}
         end
    end
  end
