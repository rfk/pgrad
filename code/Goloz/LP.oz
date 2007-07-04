
functor 
import

  Search

export

  neg: Neg
  member: Member
  union: Union

define

  % Standard negation-as-failure on a procedure
  % TODO: need to ensure that the procedure has no free variables,
  %       or the search will hang waiting for them to be bound
  %
  proc {Neg P}
    {Search.base.one proc {$ L} {P} L=unit end $} = nil
  end

  proc {Member Elem List}
    choice  List = Elem|_
    []      NewL in List=_|NewL {Member Elem NewL}
    end
  end

  proc {Union L1 L2 LF}
    case L1 of
        nil then LF = L2
    []  H|T then local LI in 
          LI = {Union T L2}
          if {Member H LI} then
            LF = LI
          else
            LF = H|LI
          end
        end
    end
  end

end

