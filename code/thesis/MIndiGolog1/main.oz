
functor

import

  LP at '/storage/uni/pgrad/code/thesis/MIndiGolog1/LP.ozf'
  Time at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Time.ozf'
  Control at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Control.ozf'
  MIndiGolog at '/storage/uni/pgrad/code/thesis/MIndiGolog1/MIndiGolog.ozf'

  Application
  Search
  Property

define

  % Make Mozart print things out to a decent depth
  %
  {Property.put 'print.width' 1000}
  {Property.put 'print.depth' 1000}
  {Property.put 'errors.width' 1000}
  {Property.put 'errors.depth' 1000}

  % Read the agent name from command-line arguments, and
  % initialise Control module accordingly
  %
  MyArgs = {Application.getArgs record(agent(single type:atom)
                                       psearch(single type:bool default:false))}
  Control.teamLeader = jon
  Control.teamMember = MyArgs.agent
  Control.doParallelSearch = MyArgs.psearch
  {Control.init}

  % Search to determine whether current state (D,S) is final
  %
  proc {IsFinal D S B} F in
    F = {Search.base.one proc {$ R} {MIndiGolog.final D S} R=unit end}
    if F == nil then B=false
    else B=true end
  end

  % Search to determine next state (Dp,Sp) from the current state (D,S)
  %
  proc {NextStep D S Dp Sp}
    [Dp#Sp] = {Search.base.one proc {$ R} DpR SpR in
                {MIndiGolog.step D S DpR SpR}
                R = DpR#SpR
              end}
  end


  % Recursive run loop, executing one step at a time until finished
  %
  proc {Run D S}
    if {IsFinal D S} then
      {Control.log succeeded}
    else Dp Sp C T in
        try 
          {NextStep D S Dp Sp}
          Sp = res(C T S)
          T = {Time.min T}
          {Control.execute C T}
          {Run Dp Sp}
        catch _ then
          {Control.log failed}
        end
    end
  end

  {Control.log start}
  {Run pcall(main) s0}

  {Application.exit 0}

end
