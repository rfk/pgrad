%
%  MutableSet.oz:  Mutable Set data type
%
%  This functor wraps the stateless 'Set' datatype in a cell, making
%  it mutable.
%

functor

import

  Set

export

  New
  Insert
  Contains
  Member
  Union
  ToList

  ToSet

define

  proc {New S}
    S = {Cell.new {Set.init}}
  end

  proc {Insert SIn E}
    OldVal in
    {Cell.exchange SIn OldVal {Set.insert OldVal E}}
  end

  proc {Contains S E B}
    {Set.contains {Cell.access S} E B}
  end

  proc {Member S E}
    {Set.member {Cell.access S} E}
  end

  proc {Union S1 S2}
    OldVal in
    if {List.is S2} then
      {Cell.exchange S1 OldVal {Set.union OldVal S2}}
    else
      S2Val = {Cell.access S2} in
      {Cell.exchange S1 OldVal {Set.union OldVal S2Val}}
    end
  end

  proc {ToList S L}
    {Set.toList {Cell.access S} L}
  end

  proc {ToSet MS S}
    S = {Cell.access MS}
  end

end
