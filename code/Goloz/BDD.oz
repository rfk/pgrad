%
%  BDD.oz:  generic binary decision diagram framework
%
%  This functor defines datastructures and procedures for operating on
%  generic BDD structures, intended for building theorem-provers that
%  work by exploring the BDD.
%
%  This module does no proving on its own.  It expects the BDD-exploring
%  procedure to be called with a "theory" object that directs the exploration
%  of the graph to implement a reasoning procedure.  It is expected to be
%  a record with the following interface:
%
%     init(D):  Initialize and return local data for path exploration
%
%     addNode(K E DIn DOut Outcome):
%               Called when a new node is added to the current path.
%               K is the node's kernel, E is the edge taken through
%               the node (0 or 1), D is the path data. Outcome
%               controls how exploration should proceed (see below).
%
%     endPath(L DIn DOut Outcome):
%               Called when a leaf node is encountered.  L is the
%               leaf node found (0 or 1).
%
%  Acceptable outcomes reported by these functions are:
%
%     ok:         the node was added, continue
%     closed:     the current path has been closed
%     stop(R):    halt exploration, return R as the result
%     extend(B):  the current path should be extended by the given BDD
%
%  The final outcome will be one of ok, closed or stop(R).
%
%  This functor exports its basic procedures as asynchronous serviecs
%  rather than vanilla procedure definitions, so that BDDs can be manipulated
%  inside subordinated spaces.  Since they have a functional interface, this
%  should be perfectly OK. The implementation versions are found in
%  I_<procname>.
%

functor 

import

  ListDict

export

  BDD
  Alias
  MemoGet
  MemoSet
  MemoCall
  ReplaceLeaves
  Explore

define

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
  %  Uses memoization to ensure canonicity.  Provided
  %  as a service for use in subordinated spaces.
  %

  proc {I_BDD Args B}
    {I_MemoCall 'bdd.bdd' Args M_BDD B}
  end

  proc {M_BDD Args B}
    [Kernel TEdge FEdge] = Args
  in
    {Exchange BDD_Count B thread B+1 end}
    {Dictionary.put BDD_Map B ite(Kernel TEdge FEdge)}
  end

  local IPort IStream in
    IPort = {Port.new IStream}
    thread
      for Args#Res in IStream do
        thread {I_BDD Args Res} end
      end
    end
    proc {BDD K T F Res}
      Res = {Port.sendRecv IPort [K T F]}
    end
  end

  %
  %  Provide facilities for memoizing arbitrary functions on BDDs.
  %  MemoGet will return a one-element list [Value], or nil if no
  %  value has yet been stored.  MemoSet will set the value in the
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
  BDD_Memo = {Dictionary.new}

  proc {I_MemoGet Funcname Args Res}
    ValD SyncValD ValM SyncValM MDict
  in
    %  Get the ListDict corresponding to that funcname.
    {Dictionary.condExchange BDD_Memo Funcname nil ValD SyncValD}
    if ValD == nil then MDict = {ListDict.new} SyncValD = [MDict]
    else SyncValD = ValD [MDict] = ValD end
    %  Find the entry corresponding to those arguments
    {ListDict.condExchange MDict Args nil ValM SyncValM}
    if ValM == nil then SyncValM = [_] Res = nil
    else [V2] = ValM in SyncValM = ValM Res=[!!V2] end
  end

  local IPort IStream in
    IPort = {Port.new IStream}
    thread
      for [Funcname Args]#Res in IStream do
        thread {I_MemoGet Funcname Args Res} end
      end
    end
    proc {MemoGet Funcname Args Res}
      Res = {Port.sendRecv IPort [Funcname Args]}
    end
  end

  proc {I_MemoSet Funcname Args Value}
    MDict = {Dictionary.get BDD_Memo Funcname}
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

  proc {I_MemoCall Funcname Args Proc Result}
    M = {I_MemoGet Funcname Args}
  in
    case M of nil then {Proc Args Result}
                       {I_MemoSet Funcname Args Result}
    else [Result]=M
    end
  end

  proc {MemoCall Funcname Args Proc Result}
    M = {MemoGet Funcname Args}
  in
    case M of nil then {Proc Args Result}
                       {MemoSet Funcname Args Result}
    else [Result]=M
    end
  end

  %
  %  Dereference the "pointer" to a BDD.
  %  Returns one of 0, 1 or ite(K T F).
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
    {MemoCall 'bdd.replaceleaves' [B TNew FNew] M_ReplaceLeaves BNew}
  end

  proc {M_ReplaceLeaves Args BNew}
    [B TNew FNew] = Args
    Bd = {Deref B}
  in
    case Bd of 0 then BNew = FNew
    []  1 then BNew = TNew
    []  ite(K T F) then BNew = {BDD K {ReplaceLeaves T TNew FNew}
                                      {ReplaceLeaves F TNew FNew}}
    else BNew=B
    end
  end

  %
  %  Mark B1 as an alias of B2.  You would typically do this if
  %  B2 is equivalent to B1 but simpler.
  %
  proc {I_Alias B1 B2}
    {Dictionary.put BDD_Map B1 alias(B2)}
  end

  local IPort IStream in
    IPort = {Port.new IStream}
    thread
      for [B1 B2]#Res in IStream do
        thread {I_Alias B1 B2} Res=unit end
      end
    end
    proc {Alias B1 B2}
      _ = {Port.sendRecv IPort [B1 B2]}
    end
  end

  %
  %  Top-level procedure for exploring a BDD.
  %  Initialize path data for the theory, then start exploring.
  %
  proc {Explore B Theory Res}
    Data = {Theory.init}
  in
    {Explore_path B Theory Data Res}
  end

  proc {Explore_path B Theory Data Res}
    ITE = {Deref B}
  in
    case ITE of ite(_ _ _) then {Explore_ITE ITE Theory Data Res}
    else {Explore_Leaf ITE Theory Data Res}
    end
  end

  proc {Explore_Leaf Leaf Theory Data Res}
    Outcome DOut
  in
    % If asked to extend, continue exploring down that path.
    % Otherwise, halt with the reported outcome.
    {Theory.endPath Leaf Data DOut Outcome}
    case Outcome of extend(B) then {Explore_path B Theory DOut Res} 
    else Res = Outcome
    end
  end

  %% TODO: allow paths to be extended in the middle?
  proc {Explore_ITE B Theory Data Res}
    ResT ResT1 ResF ResF1 DOutT DOutF
    ite(K TEdge FEdge) = B
  in
    {Theory.addNode K 1 Data DOutT ResT1}
    case ResT1 of closed then ResT = closed
    else {Explore_path TEdge Theory DOutT ResT}
    end
    case ResT of stop(V) then Res=stop(V)
    else {Theory.addNode K 0 Data DOutF ResF1}
         case ResF1 of closed then ResF = closed
         else {Explore_path FEdge Theory DOutF ResF}
         end
         case ResF of stop(V) then Res=stop(V)
         []   closed then Res = ResT
         else Res = ResF
         end
    end
  end

end

