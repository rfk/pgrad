%
%  Set.oz:  Set as abstract data type
%
%  This functor implements Sets as an abstract data type.  The implementation
%  is based on sorted lists.
%

functor

import

  LP
  Search

export

  Init
  Insert
  Contains
  Member
  Union
  ToList

  Test

define

  proc {Init S}
    S = nil
  end

  proc {Insert SIn E SOut}
    case SIn of H|Ts then
      if E == H then SOut = SIn
      elseif E < H then SOut = E|SIn
      else SOut = H|{Insert Ts E} end
    else SOut = [E] end
  end

  proc {Contains S E B}
    case S of H|Ts then
      if E == H then B = true
      else B = {Contains Ts E} end
    else B=false end
  end

  proc {Member S E}
    {LP.member E S}
  end

  proc {Union S1 S2 SOut}
    case S2 of H|Ts then
      SOut = {Union {Insert S1 H} Ts}
    else SOut = S1 end
  end

  proc {ToList S L}
    S = L
  end

  proc {Test}
    S1 S2 S3 S4 S5
  in
    S1 = {Init}
    S1 = nil
    S2 = {Insert {Insert {Insert S1 one} two} three}
    S2 = [one three two]
    S3 = {Insert {Insert {Insert S1 one} four} five}
    S3 = [five four one]
    S4 = {Union S2 S3}
    S4 = [five four one three two]
    S5 = {Union S4 [six seven eight]}
    S5 = [eight five four one seven six three two]
    {Contains S1 one false}
    {Contains S4 one true}
    {Search.base.all proc {$ E} {Member S5 E} end} = S5
  end

end
