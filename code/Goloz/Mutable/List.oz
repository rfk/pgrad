%
%  Mutable/List.oz:  Mutable List data type
%
%  This functor wraps the stateless List datatype in a cell, making it
%  mutable.
%

functor

export

  New
  Cons
  Member
  Append
  Prepend
  Length

  ToList

define

  proc {New L}
    L = {Cell.new nil}
  end

  proc {Cons L E}
    OldL in
    {Cell.exchange L OldL E|OldL}
  end

  proc {Append L Items}
    OldL in
    {Cell.exchange L OldL thread {List.append OldL Items} end}
  end

  proc {Prepend L Items}
    OldL in
    {Cell.exchange L OldL thread {List.append Items OldL} end}
  end

  proc {Length L I}
    {List.length {Cell.access L} I}
  end

  proc {Member L E B}
    {List.member E {Cell.access L} B}
  end

  proc {ToList ML L}
    L = {Cell.access ML}
  end

end
