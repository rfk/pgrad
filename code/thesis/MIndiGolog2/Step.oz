%
%  Step.oz:  procedures for handling steps of execution
%
%  A step tracks additional metadata about what actions were performed
%  and why.  It has the following attributes:
%      - action:  the action that was performed (or nil for empty steps)
%      - test:    additional conditions that held before the action
%      - thred:   the thread of execution the action was performed for
%      - out:     the observations made by each agent as a result of the action
%      - seqn:    global order in which the step was generated (sequence num)
%

functor

import

export

  Init
  Addtest
  Addthred
  Setout
  Independent

define

    %
    %  Initialize a new step object.  Missing features are
    %  given a sensible default value.
    %
    proc {Init Data Step}
      Test = {Value.condSelect Data test true}
      Act = {Value.condSelect Data action nil}
      Thred = {Value.condSelect Data thred nil}
      Out = {Value.condSelect Data out nil}
      SeqN = {Value.condSelect Data seqn ~1}
    in
      Step = step(test:Test action:Act thred:Thred out:Out seqn:SeqN)
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
    %  Determine whether the given steps are independent - that is, they
    %  can be performed in either order, or even concurrently, and the
    %  state of the world will be the same.
    %
    proc {Independent S1 S2 B}
      B = false
    end

    proc {Setout SIn Out SOut}
      SOut = {Record.adjoinAt SIn out Out}
    end

end

