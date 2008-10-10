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

export

  Init
  Get
  Put
  Append
  Drop
  DropAll
  HasLabels
  NextAvailLabels
  NextMatching
  AllMatching
  ForEach
  
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

  proc {Drop MIn I MOut}
    MOut = {Record.adjoinAt MIn entries {Record.subtract MIn.entries I}}
  end

  proc {DropAll MIn Is MOut}
    case Is of I|ITail then
      {DropAll {Drop MIn I} ITail MOut}
    else MOut = MIn end
  end

  proc {HasLabels M Lbls B}
    case Lbls of L|Ls then
      if {Value.hasFeature M.entries L} then
        B = {HasLabels M Ls}
      else B = false end
    else B = true end
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

  proc {ForEach MIn Proc MOut}
    {ForEachRec MIn 0 Proc MOut}
  end

  proc {ForEachRec MIn I Proc MOut}
    M2
  in
    if I > MIn.next then MOut = MIn
    else
      if {Value.hasFeature MIn.entries I} then NewVal in
        NewVal = {Proc I}
        M2 = {Put MIn I NewVal}
      else M2=MIn end
      {ForEachRec M2 I+1 Proc MOut}
    end
  end

end
