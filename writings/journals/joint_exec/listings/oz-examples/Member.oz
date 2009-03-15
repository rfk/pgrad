
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

