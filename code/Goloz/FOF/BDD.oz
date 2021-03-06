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
%     done(SD Outcome Res):
%               Called when exploration of the entire BDD is complete.
%               SD will be the final state data and Outcome the final
%               outcome of the exploration. Res gives what should be
%               returned from the call to {Explore}.
%
%  Acceptable outcomes reported by these functions are:
%
%     ok:         the node was added, continue
%     closed:     the current path has been closed
%     extend(B):  the current path should be extended by the given BDD
%
%  Of course the procedures may also fail, indicating that the exploration
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

  Memo at '../Utils/Memo.ozf'
  Service at '../Utils/Service.ozf'

  System

export

  bdd: BDD
  Deref
  ReplaceLeaves
  Explore

  Test

define

  %
  %  BDDs are represented as follows:
  %
  %   * 0 is a BDD representing falsehood
  %   * 1 is a BDD representing truthity
  %   * ite(Kernel TEde FEdge) is a BDD, where:
  %       - Kernel is a ground record term for a particular theory
  %       - TEdge and FEdge are BDD identifiers
  %
  %  Since memoization is used, the kernels must be fully ground terms.
  %
  %  Each BDD is identified by an integer which is treated
  %  as a pointer.  The BDD_Map dictionary derefs the pointers
  %  to give a BDD.
  %
  %  BDD_Count maintains the next free pointer value.
  %
  BDD_Count = {Cell.new 2}
  BDD_Map = {Dictionary.new}
  {Dictionary.put BDD_Map 0 0}
  {Dictionary.put BDD_Map 1 1}

  %
  %  Construct a BDD with the given kernel and edges.
  %  Uses memoization to ensure canonicity.  Provided
  %  as a service for use in subordinated spaces.
  %

  proc {I_BDD Args B}
    {Memo.memoCall 'bdd.bdd' M_BDD Args B}
  end

  proc {M_BDD Args B}
    [Kernel TEdge FEdge] = Args
    BTmp
  in
    if TEdge == FEdge then
      B = TEdge
    else
      % Don't bind the output until it is in the dictionary, to avoid races
      {Cell.exchange BDD_Count BTmp thread BTmp+1 end}
      {Dictionary.put BDD_Map BTmp ite(Kernel TEdge FEdge)}
      B = BTmp
    end
  end

  S_BDD = {Service.new I_BDD}
  proc {BDD K T F Res}
    Res = {S_BDD [K T F]}
  end

  %
  %  Dereference the "pointer" to a BDD.
  %  Returns one of 0, 1 or ite(K T F).
  %
  proc {Deref B ITE}
    ITE = {Dictionary.get BDD_Map B}
  end

  %
  %  Replace leaves of a BDD with another BDD.  B is the BDD
  %  to modify, TNew is the replacement for all 1 leaves, and FNew
  %  is the replacement for all 0 leaves.
  %

  proc {ReplaceLeaves B TNew FNew BNew}
    {Memo.memoCall 'bdd.replaceleaves' M_ReplaceLeaves [B TNew FNew] BNew}
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
  %  Top-level procedure for exploring a BDD.
  %  Initialize data for the theory, then start exploring.
  %
  proc {Explore B Theory Res}
    SDIn SDOut PData Outcome
  in
    {Theory.init SDIn PData}
    {Explore_path B Theory SDIn#SDOut PData Outcome}
    Res = {Theory.done SDOut Outcome}
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
    {Theory.endPath Leaf SDIn#SDOut1 PDIn#PDOut Out}
    case Out of extend(B) then {Explore_path B Theory SDOut1#SDOut PDOut Res} 
    else Res = Out SDOut=SDOut1
    end
  end

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
      done: proc {$ _ _ _} skip end
    )
    {Explore B Theory ok}
    @C = 4
  end

end

