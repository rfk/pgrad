%
%  FOF.oz:  (almost) first-order formulae
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
%  actuality it isn't.  All exported procedures are wrapped up in
%  asynchronous services so that they can be called in subordinated
%  spaces but still do clever things with side-effects.
%

functor 

import

  BDD

export

  Atom
  Natom
  Neg
  Conj
  Disj
  Impl
  Equiv
  All
  Exists

  ParseRecord

  Simplify

  Tautology_e
  Tautology_a
  Falsehood_e
  Falsehood_a

define

  %
  % FOF are represented by first-order shannon graphs, a BDD-like
  % structure (see BDD.oz) where the kernels may be:
  %
  %   * p(Pred) where Pred is a first-order predicate
  %   * q(SG) where SG is a shannon graph
  %
  % The terms used to construct predicates are simply Oz records in the
  % standard syntax.  However, two special record names are used to denote
  % variables:
  %
  %    * v_b(N) is a bound variable, where N is a natural number.
  %             We use de Bruijn indexing for bound variables to avoid
  %             having to rename them, and improve structure sharing.
  %
  %    * v_f(Nm) is a free variable, where Nm is an atom naming the variable.
  %              These variables are globally free in the formula, and their
  %              semantics varies depending on the type of reasoning being
  %              performed.
  %


  fun {Atom A}
    {BDD.BDD p(A) 1 0}
  end

  fun {Natom A}
    {BDD.BDD p(A) 0 1}
  end

  fun {Neg F}
    {BDD.replaceLeaves F 0 1}
  end

  fun {Conj F1 F2}
    {BDD.replaceLeaves F1 F2 0}
  end

  fun {Disj F1 F2}
    {BDD.replaceLeaves F1 1 F2}
  end

  fun {Impl F1 F2}
    {BDD.replaceLeaves F1 F2 1}
  end

  fun {Equiv F1 F2}
    {BDD.replaceLeaves F1 F2 {Neg F2}}
  end

  fun {All F}
    {BDD.BDD q(F) 1 0}
  end

  fun {Exists F}
    {BDD.BDD q({Neg F}) 0 1}
  end

  proc {ParseRecord Rec F}
    case Rec of true then F = 1
    []   false then F = 0
    []   conj(...) then case {Record.toList Rec} of nil then F = 1
                        [] H|Ts then HF = {ParseRecord H}
                                     TFs = {List.map Ts ParseRecord}
                                    in
                                     F = {List.foldL TFs Conj HF}
                        end
    []   disj(...) then case {Record.toList Rec} of nil then F = 0
                        [] H|Ts then HF = {ParseRecord H}
                                     TFs = {List.map Ts ParseRecord}
                                    in
                                     F = {List.foldL TFs Disj HF}
                        end
    []   neg(R) then F = {Neg {ParseRecord R}}
    []   impl(R1 R2) then F = {Impl {ParseRecord R1} {ParseRecord R2}}
    []   equiv(R1 R2) then F = {Equiv {ParseRecord R1} {ParseRecord R2}}
    []   all(Nm R) then F = {All {ParseRecord {BindVar Nm 0 R}}}
    []   exists(Nm R) then F = {Exists {ParseRecord {BindVar Nm 0 R}}}
    else F = {Atom Rec}
    end
  end

  proc {BindVar Nm Idx RIn ROut}
    case RIn of !Nm then ROut = v_b(Idx)
    []   all(Nm2 R2) then if Nm == Nm2 then
                            ROut = all(Nm2 R2)
                          else
                            ROut = all(Nm2 {BindVar Nm Idx+1 R2})
                          end
    []   exists(Nm2 R2) then if Nm == Nm2 then
                               ROut = exists(Nm2 R2)
                             else
                               ROut = exists(Nm2 {BindVar Nm Idx+1 R2})
                             end
    else {Record.clone RIn ROut}
         for Feature in {Record.arity RIn} do
           ROut.Feature = {BindVar Nm Idx RIn.Feature}
         end
    end
  end

  fun {Simplify F}
    F
  end

  fun {Tautology_e F}
    case F of 1 then yes
    [] 0 then no
    else unknown
    end
  end

  fun {Tautology_a F}
    {Tautology_e F}
  end

  fun {Falsehood_e F}
    case F of 1 then no
    [] 0 then yes
    else unknown
    end
  end

  fun {Falsehood_a F}
    {Falsehood_e F}
  end

end

