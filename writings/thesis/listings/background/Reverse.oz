functor

export

  Reverse

define

  proc {Reverse LIn LOut}
    case LIn of nil then
        LOut = nil
    [] H|Ts then Tr in
        {Reverse Ts Tr}
        {List.append Tr [H] LOut}
    end
  end

end
