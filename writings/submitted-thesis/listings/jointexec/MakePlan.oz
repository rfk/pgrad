
proc {MakePlan JIn Leaves JOut}
  LCls LRest
in
  {FindOpenLeaf JIn Leaves LCls LRest}
  case LRest of (D#H#N)|Ls then Dp Hp S J2 OutNs OutLs in
     {FindTrans1 D H Ls Dp Hp S}
     OutNs = {JointExec.insert JIn N S {MkPrecFunc S Hp} J2}
     OutLs = for collect:C N2 in OutNs do
                   {C Dp#ex({JointExec.getout J2 N2 S} Hp)#N2}
                end
     {MakePlan J2 {List.append LCls {List.append OutLs Ls}} JOut}
  else
    JOut = JIn
  end
end

