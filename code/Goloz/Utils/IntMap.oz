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
  NewLabels
  NextMatching
  

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
    NewI = MIn.next + 1
  in
    MOut = {Put {Record.adjoinAt MIn next NewI} NewI V}
  end

  proc {NewLabels M Items Labels}
    {NewLabels M.next Items Labels}
  end
  proc {NewLabels L Items Labels}
    case Items of _|Is then
      Labels = L|{NewLabels L+1 Is}
    else Labels = nil end
  end

  proc {NextMatching M IIn Pred IOut}
    INext = IIn + 1
  in
    if INext >= M.next then
      IOut = nil
    elseif {Value.hasFeature M.entries INext} then
      if {Pred M.entries.INext} then
        IOut = INext
      else
        {NextMathing M INext Pred IOut}
      end
    else
      {NextMathing M INext Pred IOut}
    end
  end

end
