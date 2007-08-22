%
%  BDD.oz:  generic binary decision diagram framework
%
%  This functor defines datastructures and procedures for operating on
%  generic BDD structures, intended for building theorem-provers that
%  work by exploring the BDD.
%
%  This module does no proving on its own.  Rather, it accepts registration
%  from a number of "theories" that manage the proving process.  As the BDD
%  is explored, each node is handed off on the appropriate theory.  In
%  response the theory can direct further exploration of the graph.
%
%  The implementation of this functor is complicated by the need for
%  memoization when constructing shannon graphs, combined with the need
%  to manipulate BDDs within subordinate computation spaces.
%
%   Problem:  subordinate spaces cannot mutate state in their parent space
%   Solution: run a separate thread that handles the state, and accepts
%             function calls as messages on a port
%
%  This also has the advantage of serializing access to the internal cache
%  structures, making locking unnecessary.
%

functor 

import

  RDict

export

  bdd: BDD
  alias: Alias
  memoGet: MemoGet
  memoSet: MemoSet

define

  %%%%%   Interface Functions   %%%%%

  %
  %  Interface functions send messages to this port, which are
  %  handled by a separate thread that calls the actual (private)
  %  implementation functions.
  %
  local IStream in
    IPort = {Port.new IStream}
    thread
      for Msg#Resp in IStream do
        case Msg of bdd(K T F) then Resp={I_BDD K T F}
        []  alias(B1 B2) then Resp={I_Alias B1 B2}
        []  memoGet(Func Args) then Resp={I_MemoGet Func Args}
        []  memoSet(Func Args Val) then {I_MemoSet Func Args Val} Resp=Val
        else Resp = nil
        end
      end
    end
  end

  fun {BDD K T F}
    {Port.sendRecv IPort bdd(K T F)}
  end

  fun {Alias B1 B2}
    {Port.sendRecv IPort alias(B1 B2)}
  end

  fun {MemoGet Func Args}
    {Port.sendRecv IPort memoGet(Func Args)}
  end

  proc {MemoSet Func Args Val}
    {Port.sendRecv IPort memoSet(Func Args Val)}=_
  end

  %%%%%   Implementation Functions   %%%%%

  %
  %  BDDs are represented as follows:
  %
  %   * 0 is a BDD represnting falsehood
  %   * 1 is a BDD representing truthity
  %   * ite(Kernel TEde FEdge) is a BDD, where:
  %       - Kernel is a record term for a particular theory
  %       - TEdge and FEdge are BDD identifiers
  %
  %  Each BDD is identified by an integer which is treated
  %  as a pointer.  The BDD_Map dictionary derefs the pointers
  %  to give either:
  %
  %   * a BDD
  %   * a term alias(BDD_ID)
  %
  %  The function Deref follows aliases to give the proper
  %  representation of a BDD. BDD_Count maintains the next
  %  free pointer value.
  %  
  %
  BDD_Count = {NewCell 2}
  BDD_Map = {Dictionary.new}
  {Dictionary.put BDD_Map 0 0}
  {Dictionary.put BDD_Map 1 1}

  %
  %  Construct a BDD with the given kernel and edges.
  %  Uses memoization to ensure canonicity.
  %
  proc {I_BDD Kernel TEdge FEdge B}
    M
    Key = Kernel#TEdge#FEdge
    Funcname = 'bdd.bdd'
  in
    M = {I_MemoGet Funcname Key}
    case M of nil then
        {Exchange BDD_Count B thread B+1 end}
        {I_MemoSet Funcname Key B}
        {Dictionary.put BDD_Map B ite(Kernel TEdge FEdge)}
    else [B]=M
    end
  end

  %
  %  Provide facilities for memoizing arbitrary functions on BDDs.
  %  MemoGet will return a one-element list [Value], or nil if no
  %  value has yet been stored.  MemoSet will set the value in the
  %  memo.
  %
  %  Note that MemoGet will only ever return unit *once*.  Multiple calls
  %  will return a future to the value that it assumes is being calculated.
  %  So if you call MemoGet and receive unit, you *must* then call
  %  MemoSet to give it some value.
  %
  %  Naturally, the arguments must all be things that can be stored in
  %  and RDict, i.e. they must be immutable.
  %
  BDD_Memo = {RDict.new}

  proc {I_MemoGet Funcname Args Res}
    Val MyVal
    Key = Funcname#Args
  in
    % This is for locking purposes - only one thread will receive nil,
    % the others will recieve that thread's MyVar, which will eventually
    % be made non-nil.
    {RDict.condExchange BDD_Memo Key nil Val MyVal}
    case Val of nil then MyVal = [_] Res=nil
    []  [V2] then MyVal=Val Res = [!!V2]
    else Res=nil
    end
  end

  proc {I_MemoSet Funcname Args Value}
    {RDict.get BDD_Memo Funcname#Args} = [Value]
  end


  %
  %  Dereference the "pointer" to a BDD
  %
  proc {Deref B ITE}
    Val
  in
    Val = {Dictionary.get BDD_Map B}
    case Val of alias(B2) then ITE = {Deref B2}
    else ITE = Val
    end
  end

  %
  %  Replace leaves of a BDD with another BDD.  B is the BDD
  %  to modify, TNew is the replacement for all 1 leaves, and FNew
  %  is the replacement for all 0 leaves.
  %
  proc {ReplaceLeaves B TNew FNew BNew}
    M
    Funcname = 'bdd.replaceleaves'
    Key = B#TNew#FNew
  in
    M = {MemoGet Funcname Key}
    case M of nil then Bd = {Deref B} in
        case Bd of 0 then BNew = FNew
        []  1 then BNew = TNew
        []  ite(K T F) then BNew = {BDD K {ReplaceLeaves T TNew FNew}
                                          {ReplaceLeaves F TNew FNew}}
        else BNew=B
        end
        {MemoSet Funcname Key BNew}
    else [BNew] = M
    end
  end

  %
  %  Mark B1 as an alias of B2.  You would typically do this if
  %  B2 is equivalent to B1 but simpler.
  %
  proc {I_Alias B1 B2}
    {Dictionary.put BDD_Map B1 alias(B2)}
  end

end

