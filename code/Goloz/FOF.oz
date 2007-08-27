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
  TermSet

  Search
  Browser

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
  Transform

  Simplify
  Tautology_e
  Tautology_a
  Falsehood_e
  Falsehood_a

  MemoGet
  MemoSet
  MemoCall

  Test

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

  %
  %  First, we have the basic rules for building a shannon graph for
  %  the various logical operators.
  %

  proc {Atom A F}
    F = {BDD.bdd p(A) 1 0}
  end

  fun {Natom A}
    {BDD.bdd p(A) 0 1}
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
    {BDD.bdd q(F) 1 0}
  end

  fun {Exists F}
    {BDD.bdd q({Neg F}) 0 1}
  end

  %
  %  Binding:  routines for managing a stack of variable bindings using
  %  using de Bruijn indices.  Values to be pushed are simply names.
  %  When applied to a record with {bind}, terms of the form v_b(N)
  %  are replaced with the appropriate entry from the stack.
  %  Conversely, the procedure {unbind} replaces the names on the stack
  %  with the appropriate v_b(N) term.
  %
  Binding = unit(

      init: proc {$ S}
              S=nil
            end

      push: proc {$ SIn Nm SOut}
              SOut = Nm|SIn
            end

      pop:  proc {$ SIn V SOut}
              case SIn of nil then V=nil SOut=nil
              else SIn = V|SOut
              end
            end

      getVar: proc {$ S Nm Var}
                {Binding.getVarRec S 0 Nm Var}
              end
      getVarRec: proc {$ S I Nm Var}
                   case S of nil then Var = nil
                   else N2|S2 = S in if Nm == N2 then Var = I
                                     else {Binding.getVarRec S2 I+1 Nm Var} end
                   end
                 end

      getName: proc {$ S Var Nm}
                 {Binding.getNameRec S 0 Var Nm}
               end
      getNameRec: proc {$ S I Var Nm}
                    case S of nil then Nm = v_b(Var)
                    else N2|S2=S in if Var == I then Nm = N2
                                    else {Binding.getNameRec S2 I+1 Var Nm} end
                    end
                  end

      bind: proc {$ S RIn ROut}
               case RIn of v_b(Var) then ROut = {Binding.getName S Var}
               else Fields = {Record.arity RIn} in
                    case Fields of nil then ROut = RIn
                    else {Record.clone RIn ROut}
                         for F in Fields do
                           ROut.F = {Binding.bind S RIn.F}
                         end
                    end
               end
            end

      unbind: proc {$ S RIn ROut}
                Var = {Binding.getVar S RIn}
              in
                if Var == nil then Fields = {Record.arity RIn} in
                    case Fields of nil then ROut = RIn
                    else {Record.clone RIn ROut}
                         for F in Fields do
                           ROut.F = {Binding.unbind S RIn.F}
                         end
                    end
                else ROut = v_b(Var) end
              end
  )


  %
  %  For easier writing and manipulation of formulae, this gives us
  %  the ability to construct the shannon graph for a record term.
  %  It also takes care of the variable indexing.
  %

  proc {ParseRecord Rec F}
    {ParseRecordB Rec {Binding.init} F}
  end

  proc {ParseRecordB Rec B F}
    case Rec of true then F = 1
    []   false then F = 0
    []   and(...) then case {Record.toList Rec} of nil then F = 1
                        [] H|Ts then HF = {ParseRecordB H B}
                                     M = proc {$ Q G} {ParseRecordB Q B G} end
                                     TFs = {List.map Ts M}
                                    in
                                     F = {List.foldL TFs Conj HF}
                        end
    []   'or'(...) then case {Record.toList Rec} of nil then F = 0
                        [] H|Ts then HF = {ParseRecordB H B}
                                     M = proc {$ Q G} {ParseRecordB Q B G} end
                                     TFs = {List.map Ts M}
                                    in
                                     F = {List.foldL TFs Disj HF}
                        end
    []   neg(R) then F = {Neg {ParseRecordB R B}}
    []   impl(R1 R2) then F = {Impl {ParseRecordB R1 B} {ParseRecordB R2 B}}
    []   equiv(R1 R2) then F = {Equiv {ParseRecordB R1 B} {ParseRecordB R2 B}}
    []   all(Nm R) then F = {All {ParseRecordB R {Binding.push B Nm}}}
    []   exists(Nm R) then F={Exists {ParseRecordB R {Binding.push B Nm}}}
    else F = {Atom {Binding.unbind B Rec}}
    end
  end

  proc {Transform ProcP ProcR Args Fin Fout}
    ITE = {BDD.deref Fin}
  in
    case ITE of ite(K T F) then 
        TF = {ProcR T Args}
        FF = {ProcR F Args}
       in
        case K of p(P) then KF in
          KF = {ProcP P Args}
          Fout = {BDD.replaceLeaves KF TF FF}
        [] q(Q) then QF in
          QF = q({ProcR Q Args})
          Fout = {BDD.bdd QF TF FF}
        end
    else Fout = ITE
    end
  end

  %
  %  Procedures that explore shannon graphs to do various kinds of
  %  reasoning, from straightforward simplification to full-blown
  %  theorem proving.
  %
  %  The theorem-proving procedures 'tautology' and 'falsehood' come
  %  in two flavours.  The first, suffixed with _e, tries to find some
  %  binding of the free variables in the formulae for which it is
  %  true/false.  This binding is returned in the penultimate argument.
  %  The versions suffixed with _a attempt to prove the result treating
  %  the free variables as constants, and so do not return any bindings.
  %  Of course, if there are no free variables then the two forms are
  %  equivalent.
  %

  proc {Simplify F FNew}
    F = FNew
  end

  TheoryA = unit(

    init: proc {$ Data}
            Data = path(pT: {TermSet.init}
                        pF: {TermSet.init}
                        qT: nil qF: nil)
          end

    addNode: proc {$ K E DIn DOut Res}
               case K of p(P) then
                   if E == 1 then
                       PT2 = {TermSet.put P DIn.pT} in
                       DOut = {Record.adjoinAt DIn pT PT2}
                       dis {TermSet.unify P DIn.pF} Res=closed
                       [] {TermSet.noUnify P DIn.pF} Res=ok
                       end
                   else
                       PF2 = {TermSet.put P DIn.pF} in
                       DOut = {Record.adjoinAt DIn pF PF2}
                       dis {TermSet.unify P DIn.pT} Res=closed
                       [] {TermSet.noUnify P DIn.pT} Res=ok
                       end
                   end
               [] q(Q) then
                   if E == 1 then
                       DOut = {Record.adjoinAt DIn qT (Q|DIn.qT)}
                   else
                       DOut = {Record.adjoinAt DIn qF (Q|DIn.qF)}
                   end
                   Res = ok
               else DIn = DOut Res = ok
               end
             end

    endPath: proc {$ L DIn DOut Res}
               DIn = DOut
               if L == 0 then Res = stop(open_0)
               else Res = ok end
             end

  )

  proc {Tautology_e F Binding Result}
    Binding = {Dictionary.new}
    case F of 1 then Result=yes
    [] 0 then Result=no
    else Result=unknown
    end
  end

  fun {Tautology_a F}
    Res
  in
    Res = {Search.base.one proc {$ Res} {BDD.explore F TheoryA Res} end}
    Res.1
  end

  fun {Falsehood_e F Binding}
    Binding = {Dictionary.new}
    case F of 1 then no
    [] 0 then yes
    else unknown
    end
  end

  fun {Falsehood_a F}
    {Falsehood_e F _}
  end

  %
  % Expose BDD memo functions directly
  %
  MemoGet = BDD.memoGet
  MemoSet = BDD.memoSet
  MemoCall = BDD.memoCall


  proc {Test}
    R1 = impl(and(impl(a b) impl(b c)) impl(a c))
    R2 = impl(and(impl(a b) impl(b c)) impl(d c))
    F1 F2
    Res1 Res2
  in
    F1 = {ParseRecord R1}
    Res1 = {Tautology_a F1}
    {IsDet Res1 true} Res1=ok
    F2 = {ParseRecord R2}
    Res2 = {Tautology_a F2}
    {IsDet Res2 true} Res2=stop(open_0)
  end

end

