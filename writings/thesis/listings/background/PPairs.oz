
  proc {P_AllPairs List1 List2 AllP}
    functor FindP
    import
      MyList
    export
      Script
    define
      proc {Script P}
        E1 E2
      in
        {MyList.member E1 List1}
        {MyList.member E2 List2}
        P = E1#E2
      end
    end
    Searcher = {New Search.parallel
                 init(mango:1#ssh rambutan:2#ssh)}
  in
    AllP = {Searcher all(FindP $)}
  end

