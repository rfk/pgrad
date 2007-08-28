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
%     init(SD PD):  Initialize and return local state data and path data
%
%     addNode(K E SDIn#SDOut PDIn#PDOut Outcome):
%               Called when a new node is added to the current path.
%               K is the node's kernel, E is the edge taken through
%               the node (0 or 1). Outcome controls how exploration
%               should proceed (see below).
%
%     endPath(L SDIn#SDOut PDIn#PDOut Outcome):
%               Called when a leaf node is encountered.  L is the
%               leaf node found (0 or 1).
%
%     done(SD):  Called when exploration of the entire BDD is complete.
%                SD will be the final state data.
%
%  Acceptable outcomes reported by these functions are:
%
%     ok:         the node was added, continue
%     closed:     the current path has been closed
%     extend(B):  the current path should be extended by the given BDD
%
%  Of course, the procedures may also fail to indicate the exploration
%  could not be completed. The final outcome will be either 'ok' or 'closed'.
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

  bdd: BDD
  Deref
  Alias
  MemoGet
  MemoSet
  MemoCall
  ReplaceLeaves
  Explore

  Test

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
    {I_MemoCall 'bdd.bdd' M_BDD Args B}
  end

  proc {M_BDD Args B}
    [Kernel TEdge FEdge] = Args
    BTmp
  in
    if TEdge == FEdge then
      B = TEdge
    else
      {Exchange BDD_Count BTmp thread BTmp+1 end}
      {Dictionary.put BDD_Map BTmp ite(Kernel TEdge FEdge)}
      % don't bind B until it is in the dictionary, to avoid races
      B = BTmp
    end
  end

  local IPort IStream in
    IPort = {Port.new IStream}
    thread
      for Args#Res in IStream do
        thread {I_BDD Args Res} end
      end
    end
    proc {BDD K T F Res}
      Res = !!{Port.sendRecv IPort [K T F]}
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
    [MDict] = {Dictionary.get BDD_Memo Funcname}
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

  proc {I_MemoCall Funcname Proc Args Result}
    M = {I_MemoGet Funcname Args}
  in
    case M of nil then {Proc Args Result}
                       {I_MemoSet Funcname Args Result}
    else [Result]=M
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
    {MemoCall 'bdd.replaceleaves' M_ReplaceLeaves [B TNew FNew] BNew}
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
  %  Initialize data for the theory, then start exploring.
  %
  proc {Explore B Theory Res}
    SDIn SDOut PData
  in
    {Theory.init SDIn PData}
    {Explore_path B Theory SDIn#SDOut PData Res}
    {Theory.done SDOut}
  end

  proc {Explore_path B Theory SDIn#SDOut PData Res}
    ITE = {Deref B}
  in
    case ITE of ite(_ _ _) then {Explore_ITE ITE Theory SDIn#SDOut PData Res}
    else {Explore_Leaf ITE Theory SDIn#SDOut PData Res}
    end
  end

  proc {Explore_Leaf Leaf Theory SDIn#SDOut PDIn Res}
    Out SDOut1 PDOut
  in
    % If asked to extend, continue exploring down that path.
    % Otherwise, halt with the reported outcome.
    {Theory.endPath Leaf SDIn#SDOut1 PDIn#PDOut Out}
    case Out of extend(B) then {Explore_path B Theory SDOut1#SDOut PDOut Res} 
    else Res = Out SDOut=SDOut1
    end
  end

  %% TODO: allow paths to be extended in the middle?
  proc {Explore_ITE B Theory SDIn#SDOut PDIn Res}
    SDOut1 SDOut2 SDOut3 SDOut4
    PDOutT PDOutF
    ResT1 ResT ResF1 ResF
    ite(K TEdge FEdge) = B
  in
    {Theory.addNode K 1 SDIn#SDOut1 PDIn#PDOutT ResT1}
    case ResT1 of closed then ResT = closed SDOut2=SDOut1
    else {Explore_path TEdge Theory SDOut1#SDOut2 PDOutT ResT}
    end
    {Theory.addNode K 0 SDOut2#SDOut3 PDIn#PDOutF ResF1}
    case ResF1 of closed then ResF = closed SDOut4 = SDOut3
    else {Explore_path FEdge Theory SDOut3#SDOut4 PDOutF ResF}
    end
    SDOut = SDOut4
    if ResF == closed then Res = ResT
    else Res = ResF end
  end


  proc {Test}
    {Test_memo}
    {Test_basic}
    {Test_explore}
  end

  proc {Test_basic}
    B1 B2 B3 B4
  in
    B1 = {BDD p(1 2) 1 0}
    {Deref B1} = ite(p(1 2) 1 0)
    B2 = {ReplaceLeaves B1 0 1}
    {Deref B2} = ite(p(1 2) 0 1)
    B2 = {ReplaceLeaves B1 0 1}
    B2 = {ReplaceLeaves B2 1 0}
    B1 = {ReplaceLeaves B2 0 1}
    B3 = {BDD q(B2) B1 0}
    B3 = 4
    {Deref B3} = ite(q(B2) B1 0)
    B4 = {ReplaceLeaves B3 0 1}
    {Deref B4} = ite(q(B2) B2 1)
  end

  proc {Test_memo}
    V1 V2 V3 V4 P
    C = {Cell.new 1}
  in
    {MemoGet 'bdd.test_memo' [1 2 3] V1}
    {IsFree V1 false}
    V1 = nil
    {MemoGet 'bdd.test_memo' [1 2 3] [V2]}
    {IsFuture V2 true}
    {MemoSet 'bdd.test_memo' [1 2 3] 7}
    V2 = 7
    {MemoGet 'bdd.test_memo' [1 2 3] [7]}
    proc {P _ Res}
      {Cell.exchange C Res thread Res+1 end}
    end
    {MemoCall 'bdd.test_memocall' P [4 3 2] V3}
    {IsDet V3 true}
    V3 = 1
    {MemoCall 'bdd.test_memocall' P [4 3 2] V4}
    {IsDet V4 true}
    V4 = 1
    2 = @C
  end

  proc {Test_explore}
    Theory
    B = {BDD p(a b) {BDD q(e f) 1 0} {BDD p(c d) 0 1}}
    C = {Cell.new 0}
  in
    Theory = unit(
      init: proc {$ SD PD} SD=unit PD=nil#nil end
      addNode: proc {$ K E SDIn#SDOut PDIn#PDOut Outcome}
                 Ks#Es = PDIn
               in
                 PDOut = (K|Ks)#(E|Es)
                 SDOut = SDIn
                 Outcome = ok
               end
      endPath: proc {$ L SDIn#SDOut PDIn#PDOut Outcome}
                 PDOut = PDIn
                 SDOut = SDIn
                 C := @C+1
                 Outcome = ok
               end
      done: proc {$ _} skip end
    )
    {Explore B Theory ok}
    @C = 4
  end

end

