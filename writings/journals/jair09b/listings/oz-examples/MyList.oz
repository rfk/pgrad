functor
import
Search
export
Reverse
Member
Pair
AllPairs
P_AllPairs
define

  proc {Reverse LIn LOut}
    case LIn of nil then
        LOut = nil
    [] H|Ts then Tr in
        {Reverse Ts Tr}
        {List.append Tr [H] LOut}
    end
  end


  proc {Member E List}
    case List of nil then
        fail
    [] H|Ts then
        choice
            E = H
        []
            {Member E Ts}
        end
    end
  end


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


  proc {P_AllPairs List1 List2 AllP}
    functor FindP
    export
      Script
    define
      proc {Script P}
          E1 E2
      in
          {Member E1 List1}
          {Member E2 List2}
          P = E1#E2
      end
      proc {Member E List}
        case List of nil then fail
        [] H|Ts then choice E = H [] {Member E Ts} end
        end
      end
    end
    Searcher = {New Search.parallel init(mango:1#ssh rambutan:2#ssh)}
  in
    AllP = {Searcher all(FindP $)}
  end

end
