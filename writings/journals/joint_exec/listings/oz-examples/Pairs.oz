
  proc {Pair List1 List2 P}
    E1 E2
  in
    {Member E1 List1}
    {Member E2 List2}
    P = E1#E2
  end

  proc {AllPairs List1 List2 AllP}
    FindP = proc {$ P}
              {Pair List1 List2 P}
            end
  in
    AllP = {Search.base.all FindP}
  end

