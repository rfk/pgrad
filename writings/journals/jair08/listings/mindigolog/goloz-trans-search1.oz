proc {Trans D S Dp Sp}
  [] ... 
  []   search(D1) then Sr Dr in
                  {Trans D1 S Dr Sp}
                  {Do Dr Sp Sr}
                  Dp = dosteps({Sitcalc.toStepsList Sp Sr})
  []   dosteps(Steps) then C T Steps2 in
                  Steps = (C#T)|Steps2
                  Sp = res(C T S)
                  Dp = dosteps(Steps2)
  [] ...
end
