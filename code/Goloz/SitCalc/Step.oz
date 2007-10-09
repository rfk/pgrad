%
%  Step.oz:  procedures for handling steps of execution
%
%  A step tracks additional metadata about what actions were performed
%  and why.  It pairs an action with the following info:
%      - test:  additional conditions that held before the action
%      - thred: indicates the thread of execution the action was performed
%               in service of
%      - obs:   indicates the observations made by each agent as a result
%               of performing the action.
%

functor

import

  LP at '../Utils/LP.ozf'
  SitCalc

  Search

export

  Init
  Addtest
  Addthred
  Addobs
  Getobs
  Independent

define

    %
    %  Initialize a new step object.  Missing features are
    %  given a sensible default value.
    %
    proc {Init Data Step}
      Test = {Value.condSelect Data test true}
      ActT = {Value.condSelect Data action nil}
      Act = if {List.is ActT} then {List.sort ActT Value.'<'} else [ActT] end
      Thred = {Value.condSelect Data thred nil}
      Obs = {Value.condSelect Data obs nil}
    in
      Step = step(test:Test action:Act thred:Thred obs:Obs)
    end

    %
    %  Add an additional test condition to the step
    %
    proc {Addtest SIn C SOut}
      SOut = {Record.adjoinAt SIn test and(C SIn.test)}
    end

    %
    %  Push an additional thread identifier for the step
    %
    proc {Addthred SIn T SOut}
      SOut = {Record.adjoinAt SIn thred T|SIn.thred}
    end

    %
    %  Add some observations to the step.
    %  O is map from agents to the observations they made.
    %
    proc {Addobs SIn O SOut}
      O2 = {SitCalc.newAgentMap}
      for Agt in {Record.arity O2} do
        O2.Agt = {List.append {Value.condSelect O Agt nil}
                              {Value.condSelect SIn.obs Agt nil}}
      end
      SOut = {Record.adjoinAt SIn obs O2}
    end

    proc {Getobs S Agt Obs}
      Obs = {Value.condSelect S.obs Agt nil}
    end

    %
    %  Determine whether the given steps are independent - that is, they
    %  can be performed in either order, or even concurrently, and the
    %  state of the world will be the same.
    %
    proc {Independent S1 S2 B}
      B = false
    end

end

