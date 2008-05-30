  proc {Plan D J}
    {MakePlan {JointExec.init} [D#now#nil] J}
  end

  proc {MakePlan JIn Branches JOut}
    BClosed BRest
  in
    {FindOpenBranch JIn Branches BClosed BRest}
    case BRest of (D#R#N)|Bs then Dp Rp S J2 OutNs OutBs in
       {FindTrans1 D R Dp Rp S}
       OutNs = {JointExec.insert JIn N S {MkPrecFunc S Rp} J2}
       OutBs = for collect:C N2 in OutNs do
                   {C Dp#ex({JointExec.getobs J2 N2 S} Rp)#N2}
                end
       {MakePlan J2 {Append3 BClosed OutBs Bs} JOut}
    else JOut = JIn end
  end

  proc {FindOpenBranch J Branches BClosed BRest}
    case Branches of (D1#R1#N1)|Bs then D R N NewBs in
        (D#R#N)|NewBs = {HandleExistingEvents J D1#R1#N1}
        if {ConGolog.isFinal D R} then BC2
          BClosed = (D#R#N)|BC2
          {FindOpenBranch J {List.append NewBs Bs} BC2 BRest}
        else
          BClosed = nil BRest = (D#R#N)|{List.append NewBs Bs}
        end
    else BClosed = nil BRest = nil end
  end

  proc {FindTrans1 D R Dp Rp S}
    Searcher SearchProc
  in
    proc {SearchProc Q} Dp Rp S in
      {ConGolog.trans1 D R Dp Rp S}
      Q = Dp#Rp#S
    end
    Searcher = {New Search.object script(SearchProc)}
    Dp#Rp#S = {LP.yieldOrdered Searcher CompareSteps}
  end
