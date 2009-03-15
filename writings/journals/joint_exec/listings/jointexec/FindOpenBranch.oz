
proc {FindOpenLeaf J Leaves LCls LRest}
  case Leaves of (D1#H1#N1)|Ls then D H N NewLs in
      (D#H#N)|NewLs = {HandleExistingEvents J D1#H1#N1}
      if {MIndiGolog.isFinal D H} then
        LCls = (D#H#N)|_
        {FindOpenLeaf J {List.append NewLs Ls} LCls.2 LRest}
      else
        LClosed = nil LRest = (D#H#N)|{List.append NewLs Ls}
      end
  else LCls = nil LRest = nil end
end

