%
%  BDD.oz:  generic binary decision diagram framework
%
%  This functor defines datastructures and procedures for operating on
%  generic BDD structures, intended for building theorem-provers that
%  work by exploring the BDD.
%
%  This module does no proving on its own.  It expects the BDD-exploring
%  procedure to be called with a list of "theories" that implement specific
%  aspects of reasoning.  They are expected to be records with the following
%  interface:
%
%     init(D):  Initialize and return local data for path exploration
%
%     addNode(K E DIn DOut Outcome):
%               Called when a new node is added to the current path.
%               K is the node's kernel, E is the edge taken through
%               the node (0 or 1), D is the path data, and Outcome
%               controls how exploration should proceed.  This is
%               called for every theory in the list.  Outcome may
%               be:  ok, closed
%
%     endPath(L DIn DOut Outcome):
%               Called when a leaf node is encountered.  L is the
%               leaf node found (0 or 1).  This is called until
%               a theory responds with extend(B R) or all theories
%               have been tried.  Outcome may be: ok, extend(B R)
%
%     termPath(L D Outcome):
%               Called when a leaf node has been encountered and
%               was not extended by a call to endPath for any theory.
%               Note that this cannot alter the path data.
%               Outcome may be: ok, closed, stop(R)
%
%  Acceptable outcomes reported by these functions are:
%
%     ok:         the node was added, continue
%     closed:     the current path has been closed
%     stop(R):    halt exploration, return R as the result
%     extend(B R):  the current path should be extended by the given BDD,
%                   renamed according to R
%
%  The final outcome will be one of ok, closed or stop(R).
%

functor 

import

  RDict
  LP

export

  bdd: BDD
  alias: Alias
  memoGet: MemoGet
  memoSet: MemoSet
  explore: Explore

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
  %  Uses memoization to ensure canonicity.
  %
  proc {BDD Kernel TEdge FEdge B}
    M
    Key = Kernel#TEdge#FEdge
    Funcname = 'bdd.bdd'
  in
    M = {MemoGet Funcname Key}
    case M of nil then
        {Exchange BDD_Count B thread B+1 end}
        {MemoSet Funcname Key B}
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
  %  Note that MemoGet will only ever return nil *once*.  Multiple calls
  %  will return a future to the value that it assumes is being calculated.
  %  So if you call MemoGet and receive nil, you *must* then call
  %  MemoSet to give it some value.
  %
  %  Naturally, the arguments must all be things that can be stored in
  %  an RDict, i.e. they must be immutable.
  %
  BDD_Memo = {RDict.new}

  proc {MemoGet Funcname Args Res}
    Val MyVal
    Key = Funcname#Args
  in
    % This is for locking purposes - only one thread will receive nil,
    % the others will recieve that thread's MyVar, which will eventually
    % be made non-nil.  They syncronise it to their own variable.
    {RDict.condExchange BDD_Memo Key nil Val MyVal}
    case Val of nil then MyVal = [_] Res=nil
    []  [V2] then MyVal=Val Res = [!!V2]
    else Res=nil
    end
  end

  proc {MemoSet Funcname Args Value}
    {RDict.get BDD_Memo Funcname#Args} = [Value]
  end


  %
  %  Dereference the "pointer" to a BDD.
  %  Returns one of 0, 1 or ite(B T F).
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
  proc {Alias B1 B2}
    {Dictionary.put BDD_Map B1 alias(B2)}
  end

  %
  %  Top-level procedure for exploring a BDD.
  %  Initialize path data for each theory, then start exploring
  %
  proc {Explore B Rn Theories Res}
    Data = {List.map Theories proc {$ T D} {T.init D} end}
  in
    {Explore_path B Rn Theories Data Res}
  end

  proc {Explore_path B Rn Theories Data Res}
    ITE = {Deref B}
  in
    case ITE of ite(_ _ _) then {Explore_ITE ITE Rn Theories Data Res}
    else {Explore_Leaf ITE Rn Theories Data Res}
    end
  end

  proc {Explore_Leaf Leaf Rn Theories Data Res}
    Outcome DOut RnOut
  in
    {Explore_endPath Leaf Theories Data DOut Outcome}
    case Outcome of ok then {Explore_termPath Leaf Theories DOut Res}
    else extend(B Rn2) = Outcome in {Explore_RenameAdd Rn Rn2 RnOut}
                                    {Explore_path B RnOut Theories DOut Res} 
    end
  end

  %%  TODO:  do we need to enforce fairness between theories?
  proc {Explore_endPath Leaf Theories DIn DOut Outcome}
    case Theories of nil then Outcome = ok DOut = nil
    else THead|TTail = Theories
         DHead|DTail = DIn
         Out2 DOutHead DOutTail
        in
         DOut = DOutHead|DOutTail
         {THead.endPath Leaf DHead DOutHead Out2}
         case Out2 of extend(B R) then Outcome = extend(B R) DOutTail=DTail
         else {Explore_endPath Leaf TTail DTail DOutTail Outcome}
         end
    end
  end

  proc {Explore_termPath Leaf Theories Data Res}
    case Theories of nil then Res = ok
    else THead|TTail = Theories
         DHead|DTail = Data
         Out2
        in
         {THead.termPath Leaf DHead Out2}
         case Out2 of closed then Res = closed
         []  stop(V) then Res = stop(V)
         else {Explore_termPath Leaf TTail DTail Res}
         end
    end
  end

  proc {Explore_ITE B Rn Theories Data Res}
    OutT OutT1 OutF OutF1
    DOutT DOutF Kr
    ite(K TEdge FEdge) = B
  in
    Kr = {Explore_Rename K Rn}
    {Explore_addNode Kr 1 Theories Data DOutT OutT1}
    case OutT1 of closed then OutT = closed
    else {Explore_path TEdge Rn Theories DOutT OutT}
    end
    case OutT of stop(V) then Res=stop(V)
    else {Explore_addNode Kr 0 Theories Data DOutF OutF1}
         case OutF1 of closed then OutF = closed
         else {Explore_path FEdge Rn Theories DOutF OutF}
         end
         case OutF of stop(V) then Res=stop(V)
         []   closed then Res = OutT
         else Res = OutF
         end
    end
  end

  proc {Explore_addNode K E Theories Data DOut Res}
    case Theories of nil then Res = ok DOut = nil
    else THead|TTail = Theories
         DHead|DTail = Data
         DOutHead DOutTail Outcome
        in
         DOut = DOutHead|DOutTail
         {THead.addNode K E DHead DOutHead Outcome}
         case Outcome of closed then Res=closed
         else {Explore_addNode K E TTail DTail DOutTail Res}
         end
    end
  end

  proc {Explore_Rename TIn Rn TOut}
    case Rn of nil then TIn = TOut
    else T2 Old#New|RnT = Rn in {LP.subInTerm Old New TIn T2}
                                {Explore_Rename T2 RnT TOut}
    end
  end

  proc {Explore_RenameAdd Rn1 Rn2 RnOut}
    {Explore_RenameAddAcc Rn1 Rn2 nil RnOut}
  end

  proc {Explore_RenameAddAcc Rn1 Rn2 RnAcc RnOut}
    case Rn1 of nil then RnOut = {List.append Rn2 RnAcc}
    else Old#New|Rn1T = Rn1
        in
         if {Explore_RenameContains Rn2 Old} then
           {Explore_RenameAddAcc Rn1T Rn2 RnAcc RnOut}
         else
           {Explore_RenameAddAcc Rn1T Rn2 Old#New|RnAcc RnOut}
         end
    end
  end

  proc {Explore_RenameContains Rn Old B}
    case Rn of nil then B = false
    else ROld#_|RnT = Rn
        in
         B = if ROld == Old then true else {Explore_RenameContains RnT Old} end
    end
  end

end

