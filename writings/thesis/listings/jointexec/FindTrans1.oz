
  proc {FindTrans1 D R Bs Dp Rp S}
    Searcher SearchProc
  in
    proc {SearchProc Q} Dp Rp S in
      {MIndiGolog.trans1 D R Dp Rp S}
      Q = Dp#Rp#S
    end
    Searcher = {New Search.object script(SearchProc)}
    Dp#Rp#S = {LP.yieldOrdered Searcher CompareTrans1}
  end

