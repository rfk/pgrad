proc {Trans D S Dp Sp}
  [] ... 
  [] search(D1) then Sr Dr in
          if Control.teamMember == Control.teamLeader then
               try
                 {Trans D1 S Dr Sp}
                 {ParallelDo Dr Sp Sr}
                 Dp = dosteps({Sitcalc.toStepsList Sp Sr})
                 {Control.sendMessage Dp#Sp}
               catch failure then
                 {Control.sendMessage plan_failed}
                 fail
               end
           else Msg in
               {Control.waitForMessage Msg}
               if Msg == plan_failed then
                 fail
               else
                 (Dp#Sp) = Msg
               end
           end
  [] ...
end
