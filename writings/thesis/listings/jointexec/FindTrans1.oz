
proc {FindTrans1 D H Ls Dp Rp S}
  Searcher SearchProc
in
  proc {SearchProc Q} Dp Hp S in
    {MIndiGolog.trans1 D H Dp Hp S}
    Q = Dp#Hp#S
  end
  Searcher = {New Search.object script(SearchProc)}
  Dp#Rp#S = {LP.yieldOrdered Searcher CompareTrans1}
end

