%
%  Memo.oz:  facilities to memoize function calls
%
%  {MemoGet FuncName [Args] Result} will return a one-element list [Value],
%  or nil if no value has yet been stored.  MemoSet will set the value in the
%  memo.
%
%  Note that MemoGet will only ever return nil *once*.  Multiple calls
%  will return a future to the value that it assumes is being calculated.
%  So if you call MemoGet and receive nil, you *must* then call
%  MemoSet to give it some value.
%
%  To conveniently deploy a memoized function, use MemoCall, passing it
%  a reference to another procedure that will calculate the value if
%  it is missing.
%
%  Naturally, the arguments must all be immutable for this to work.
%
%

functor 

import

  ListDict

export

  MemoGet
  MemoSet
  MemoCall

  Test

define

  Memo = {Dictionary.new}

  proc {I_MemoGet Funcname Args Res}
    ValD SyncValD ValM SyncValM MDict
  in
    %  Get the ListDict corresponding to that funcname.
    {Dictionary.condExchange Memo Funcname nil ValD SyncValD}
    if ValD == nil then MDict = {ListDict.new} SyncValD = [MDict]
    else SyncValD = ValD [MDict] = ValD end
    %  Find the entry corresponding to those arguments
    {ListDict.condExchange MDict Args nil ValM SyncValM}
    if ValM == nil then SyncValM = [_] Res = nil
    else [V2] = ValM in SyncValM = ValM Res = [!!V2] end
  end

  local IPort IStream in
    IPort = {Port.new IStream}
    thread
      for [Funcname Args]#Res in IStream do
        thread {I_MemoGet Funcname Args Res} end
      end
    end
    proc {MemoGet Funcname Args Res}
      Res = !!{Port.sendRecv IPort [Funcname Args]}
    end
  end

  proc {I_MemoSet Funcname Args Value}
    [MDict] = {Dictionary.get Memo Funcname}
  in
    {ListDict.get MDict Args} = [Value]
  end

  local IPort IStream in
    IPort = {Port.new IStream}
    thread
      for [Funcname Args Val]#Res in IStream do
        thread {I_MemoSet Funcname Args Val} Res=unit end
      end
    end
    proc {MemoSet Funcname Args Val}
      _ = {Port.sendRecv IPort [Funcname Args Val]}
    end
  end

  proc {MemoCall Funcname Proc Args Result}
    M = {MemoGet Funcname Args}
  in
    case M of nil then {Proc Args Result}
                       {MemoSet Funcname Args Result}
    else [Result]=M
    end
  end

  proc {Test}
    V1 V2 V3 V4 P
    C = {Cell.new 1}
  in
    {MemoGet 'memo.test_memo' [1 2 3] V1}
    {IsFree V1 false}
    V1 = nil
    {MemoGet 'memo.test_memo' [1 2 3] [V2]}
    {IsFuture V2 true}
    {MemoSet 'memo.test_memo' [1 2 3] 7}
    V2 = 7
    {MemoGet 'memo.test_memo' [1 2 3] [7]}
    proc {P _ Res}
      {Cell.exchange C Res thread Res+1 end}
    end
    {MemoCall 'memo.test_memocall' P [4 3 2] V3}
    {IsDet V3 true}
    V3 = 1
    {MemoCall 'memo.test_memocall' P [4 3 2] V4}
    {IsDet V4 true}
    V4 = 1
    2 = @C
  end

end
