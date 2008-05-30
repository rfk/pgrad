  proc {Trans D R Dp Sp}
    case D of 
        test(Cond) then
          {SitCalc.holds R Cond}
          Dp = nil
          Sp = {Step.init step(test:Cond)}
  <--  additional cases ommitted -->
    []  conc(D1 D2) then
          choice D1p S1p in
              {Trans D1 R D1p S1p}
              Dp=conc(D1p D2)  Sp={Step.addthred S1p l}
          []  D2p S2p in
              {Trans D2 R D2p S2p}
              Dp=conc(D1 D2p)  Sp={Step.addthred S2p r}
          end
  end
