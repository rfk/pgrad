%
%  FOF.oz:  first-order formulae (almost)
%
%  This functor defines datastructures and procedures for operating
%  on first-order formulae as an abstract data type.  The implementation
%  is currently based on shannon graphs with a simple reasoning procedure
%  that is "complete enough" for our purposes.
%
%  We make the following restrictions to make reasoning easier:
%
%    * all functions are unique names, so unification decides equality
%    * variables all range over finite domains
%
%  The interface may be treated as being side-effect free, although in
%  actualality it isn't.  All exported procedures are wrapped up in
%  asynchronous services so that they can be called in subordinated
%  spaces but still do clever things with side-effects.
%

functor 

import

  BDD
  Service

export

  atom: I_Atom
  natom: I_NAtom
  neg: I_Neg
  conj: I_Conj
  disj: I_Disj
  impl: I_Impl
  equiv: I_Equiv
  all: I_All
  exists: I_Exists

  simplify: I_Simplify

  tautology: I_Tautology
  falsehood: I_Falsehood

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
        case Msg of atom(A) then Resp={Atom A}
        []   natom(A) then Resp={NAtom A}
        []   neg(F) then Resp={Neg F}
        []   conj(F1 F2) then Resp={Conj F1 F2}
        []   disj(F1 F2) then Resp={Disj F1 F2}
        []   impl(F1 F2) then Resp={Impl F1 F2}
        []   equiv(F1 F2) then Resp={Equiv F1 F2}
        []   all(F) then Resp={All F}
        []   exists(F) then Resp={Exists F}
        []   simplify(F) then Resp={Simplify F}
        []   reallySimplify(F) then Resp={ReallySimplify F}
        []   tautology(F) then Resp={Tautology F}
        []   falsehood(F) then Resp={Falsehood F}
        else Resp = nil
        end
      end
    end
  end

  fun {I_Atom A}
    {Port.sendRecv IPort atom(A)}
  end

  fun {I_NAtom A}
    {Port.sendRecv IPort natom(A)}
  end

  fun {I_Neg F}
    {Port.sendRecv IPort neg(F)}
  end

  fun {I_Conj F1 F2}
    {Port.sendRecv IPort conj(F1 F2)}
  end

  fun {I_Disj F1 F2}
    {Port.sendRecv IPort disj(F1 F2)}
  end

  fun {I_Impl F1 F2}
    {Port.sendRecv IPort impl(F1 F2)}
  end

  fun {I_Equiv F1 F2}
    {Port.sendRecv IPort equiv(F1 F2)}
  end

  fun {I_All F}
    {Port.sendRecv IPort all(F)}
  end

  fun {I_Exists F}
    {Port.sendRecv IPort exists(F)}
  end

  fun {I_Simplify F}
    {Port.sendRecv IPort simplify(F)}
  end

  fun {I_ReallySimplify F}
    {Port.sendRecv IPort reallySimplify(F)}
  end

  fun {I_Tautology F}
    {Port.sendRecv IPort tautology(F)}
  end

  fun {I_Falsehood F}
    {Port.sendRecv IPort falsehood(F)}
  end


  %%%%%   Implementation Functions   %%%%%

  %
  % FOF are represented by first-order shannon graphs, a BDD-like
  % structure defined as follows:
  %
  %   * 0 is a shannon graph represnting falsehood
  %   * 1 is a shannon graph representing truthity
  %   * ite(Kernel TEde FEdge) is a shannon graph, where:
  %       - Kernel is a shannon kernel, defined below
  %       - TEdge and FEdge are shannon graphs
  %
  % A shannon kernel is:
  %   * p(Pred) where Pred is a first-order predicate
  %   * q(SG) where SG is a shannon graph
  %
  % The terms used to construct predicates are simply Oz records in the
  % standard syntax.  However, the special function v_(N) is reserved
  % for variables, where N is an integer.  N represents the number of
  % quantifiers between the occurance of the variable and its binding.
  % TODO: find the reference for this technique
  %

  %
  %  Each FOSG is identified by an integer which is treated
  %  as a pointer.  The FOSG_Map dictionary derefs the pointer to
  %  give the kernel of the graph as well as its T and F edges.
  %  FOSG_Count maintains the next free pointer value.
  %
  FOSG_Count = {NewCell 2}
  FOSG_Map = {Dictionary.new}
  {Dictionary.put FOSG_Map 0 0}
  {Dictionary.put FOSG_Map 1 1}

  %
  %  FOSG_Cache is used for memoization when creating graphs.
  %  FOSG_Funcache is used for memoization of other procedure calls.
  %
  FOSG_Cache = {RDict.new}
  FOSG_Funcache = {RDict.new}

  %
  %  Construct a shannon graph with the given kernel and edges.
  %  Uses FOSG_Cache for memoization.
  %
  proc {MakeFOSG Kernel TEdge FEdge G}
    Cached
  in
    Cached = {RDict.condGet FOSG_Cache Kernel#TEdge#FEdge unit}
    case Cached of unit then
        {Exchange FOSG_Count G thread G+1 end}
        {RDict.put FOSG_Cache Kernel#TEdge#FEdge G}
        {Dictionary.put FOSG_Map G ite(Kernel TEdge FEdge)}
    else
        G = Cached
    end
  end

  %
  %  Dereference the "pointer" to a FOSG
  %
  proc {Deref Graph ITE}
    ITE = {Dictionary.get FOSG_Map Graph}
  end

  %
  %  Replace elements inside a shannon graph with a different graph.
  %  Graph is the FOSG to modify, Repls is a list of Old#New graph
  %  pairs to be simultaneously replaced, and NewG is the resulting graph.
  %
  proc {Replace Graph Repls NewG}
    Cache
  in
    Cache = {RDict.condGet FOSG_Funcache replace#Graph#Repls unit}
    case Cache of unit then GRepl in
        GRepl = {PairSearch Repls Graph}
        case GRepl of unit then
            case {Deref Graph} of 0 then NewG = 0
            [] 1 then NewG = 1
            [] ite(K T F) then NewG = {MakeFOSG K {Replace T Repls} {Replace F Repls}}
            end
        else NewG = GRepl
        end
        {RDict.put FOSG_Funcache replace#Graph#Repls NewG}
    else NewG = Cache
    end
  end

  proc {PairSearch List Key Value}
    case List of nil then Value=unit
    [] H|T then
      case H of !Key#V then Value=V
      else {PairSearch T Key Value}
      end
    end
  end

  fun {Atom A}
    {MakeFOSG A 1 0}
  end

  fun {NAtom A}
    {MakeFOSG A 0 1}
  end

  fun {Neg F}
    {Replace F [1#0 0#1]}
  end

  fun {Conj F1 F2}
    {Replace F1 [1#F2]}
  end

  fun {Disj F1 F2}
    {Replace F1 [0#F2]}
  end

  fun {Impl F1 F2}
    {Replace F1 [0#1 1#F2]}
  end

  fun {Equiv F1 F2}
    {Replace F1 [0#{Neg F2} 1#F2]}
  end

  fun {All F}
    {MakeFOSG F 1 0}
  end

  fun {Exists F}
    {MakeFOSG {Neg F} 0 1}
  end

  fun {Simplify F}
    F
  end

  fun {ReallySimplify F}
    {Simplify F}
  end

  fun {Tautology F}
    case F of 1 then yes
    [] 0 then no
    else unknown
    end
  end

  fun {Falsehood F}
    case F of 1 then no
    [] 0 then yes
    else unknown
    end
  end

end

