
functor 
import

  Search

export

  neg: Neg
  member: Member

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

end

