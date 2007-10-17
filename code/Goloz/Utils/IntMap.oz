%
%  IntMap.oz:  immutable map from integers to values
%
%  Yes, this is basically an integer-keyed hash table.  But it's a much
%  nicer interface than manipulating records explicitly. Also mozart
%  folklore says that creating many different record arities is
%  bad for performance, so we can toy around with it in the luxury of
%  an abstract data type.
%

functor

import

  System

export

  Init
  Get
  Put
  Append
  NextAvailLabels
  NextMatching
  AllMatching
  ForEach
  
  Test

define

  proc {Init M}
    M = intmap(next: 0 entries: unit)
  end

  proc {Get M I V}
    V = M.entries.I
  end

  proc {Put MIn I V MOut}
    MOut = {Record.adjoinAt MIn entries {Record.adjoinAt MIn.entries I V}}
  end

  proc {Append MIn V MOut}
    MOut = {Put {Record.adjoinAt MIn next MIn.next+1} MIn.next V}
  end

  proc {NextAvailLabels M Items Labels}
    {NextAvailLabelsRec M.next Items Labels}
  end
  proc {NextAvailLabelsRec L Items Labels}
    case Items of _|Is then
      Labels = L|{NextAvailLabelsRec L+1 Is}
    else Labels = nil end
  end

  proc {NextMatching M IIn Pred IOut}
    INext = IIn + 1
  in
    if INext >= M.next then
      IOut = nil
    elseif {Value.hasFeature M.entries INext} then
      if {Pred INext} then
        IOut = INext
      else
        {NextMatching M INext Pred IOut}
      end
    else
      {NextMatching M INext Pred IOut}
    end
  end

  fun {AllMatching M Pred}
    {AllMatchingRec M 0 Pred}
  end

  fun lazy {AllMatchingRec M I Pred}
    if I > M.next then nil
    else
      if {Value.hasFeature M.entries I} then
        if {Pred I} then
          I|{AllMatchingRec M I+1 Pred}
        else
          {AllMatchingRec M I+1 Pred}
        end
      else
        {AllMatchingRec M I+1 Pred}
      end
    end
  end

  proc {ForEach M Proc}
    {ForEachRec M 0 Proc}
  end

  proc {ForEachRec M I Proc}
    if I > M.next then skip
    else
      if {Value.hasFeature M.entries I} then
        {Proc I}
      end
      {ForEachRec M I+1 Proc}
    end
  end

  proc {Test}
    M1 M2
  in
    M1 = {Init}
    M1.next = 0
    M1.entries = unit
    M2 = {Append {Append M1 test1} test2}
    M2.next = 2
    {Get M2 0} = test1
    {Get M2 1} = test2
    {NextMatching M2 0 fun {$ _} true end} = 1
  end

end
