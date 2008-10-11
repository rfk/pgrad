
  proc {FindOpenBranch J Branches BClosed BRest}
    case Branches of (D1#R1#N1)|Bs then D R N NewBs in
        (D#R#N)|NewBs = {HandleExistingEvents J D1#R1#N1}
        if {MIndiGolog.isFinal D R} then
          BClosed = (D#R#N)|_
          {FindOpenBranch J {List.append NewBs Bs} BClosed.2 BRest}
        else
          BClosed = nil BRest = (D#R#N)|{List.append NewBs Bs}
        end
    else BClosed = nil BRest = nil end
  end

