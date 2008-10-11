
  proc {MakePlan JIn Branches JOut}
    BClosed BRest
  in
    {FindOpenBranch JIn Branches BClosed BRest}
    case BRest of (D#R#N)|Bs then Dp Rp S J2 OutNs OutBs in
       {FindTrans1 D R Bs Dp Rp S}
       OutNs = {JointExec.insert JIn N S {MkPrecFunc S Rp} J2}
       OutBs = for collect:C N2 in OutNs do
                     {C Dp#ex({JointExec.getobs J2 N2 S} Rp)#N2}
                  end
       {MakePlan J2 {List.append BClosed {List.append OutBs Bs}} JOut}
    else
      JOut = JIn
    end
  end

