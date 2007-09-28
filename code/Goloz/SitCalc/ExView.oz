%
%  ExView.oz:  agent-specific view of an Execution.
%


functor

import

  Step
  Exec

export

  Consistent

define

  proc {NextSteps Agt ExIn ExOuts}
    ExOuts = for collect:C Ex2 in {Exec.nextSteps ExIn} do
               if {Step.getobs Agt Ex2.past.1.2} == nil then
                 for Ex3 in {NextSteps Agt Ex2} do
                   {C Ex3}
                 end
               else
                 {C Ex2}
               end
             end
  end

  proc {Consistent Agt E2 E2 B}
    
  end

end
