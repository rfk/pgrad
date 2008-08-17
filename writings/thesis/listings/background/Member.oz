functor

export

  Member

define

  proc {Member E List}
    case List of nil then
        fail
    [] H|Ts then Tr in
        {Reverse Ts Tr}
        {List.append Tr [H] LOut}
    end
  end

end
