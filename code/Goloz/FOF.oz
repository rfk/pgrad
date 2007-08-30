%
%  FOF.oz:  (almost) first-order formulae
%
%  This functor defines datastructures and procedures for operating
%  on first-order formulae as an abstract data type.  The implementation
%  is currently based on shannon graphs with a simple reasoning procedure
%  that is "complete enough" for our purposes.
%
%  We use the following assumption to make reasoning easier:
%
%    * all functions are unique names, so unification decides equality
%
%  Coupled with an "essentially propositional" domain, this gives a
%  decision procedure for entailment in the logic.
%
%  The interface may be treated as being side-effect free (although in
%  actuality it does some clever memoization and other tricks).
%
%  This functor exports a free variable in FOF.lang, which importing
%  modules should instantiate with a structure describing the particular
%  language they are proving in.  It should have the following features:
%
%     FOF.lang.wff:  a procedure that takes a predicate in the language,
%                    and posts constraints ensuring that if is well formed.
%                    For example, this might post constraints about the
%                    domains of variables, inferring their type from their
%                    location in the predicate.
%
%  This is done using a free variable rather than e.g. a cell because it
%  affects memoization and other features of the module.  Each consumer of
%  this module should use {Module.link} to create their own private
%  copy.
%

functor 

import

  LP
  BDD
  TermSet
  QuantSet
  EQSet

  Search
  System

export

  ParseRecord
  Transform
  Lang

  Atom
  Natom
  Neg
  Conj
  Disj
  Impl
  Equiv
  All
  Exists

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
  %    * v_e(Nm) is an free existentially-quantified variable. Nm is
  %              a (globally unique) name for the variable.  These are
  %              internally translated into the form v_e(Nm V) during
  %              proof search, where V is a free Oz variable used to
  %              constrint the values tekn by the variable.  This setup
  %              avoid accidentally binding V during the search.
  %
  % If you use the {ParseRecord} procedure to construct your formulae, you
  % need only worry about free variables, bound variables will be created
  % automatically.
  %
  % We use terms of the form v_e(skv(N)) for skolem variables internally.
  % Dont name your free variables like this unless you want to break things.
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
  %  Binding:  routines for managing a stack of variable bindings
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
  %  To allow consumers to determine the language we operate on,
  %  expose the free variable Lang
  %
  Lang = _

  %
  %  For easier writing and manipulation of formulae, this gives us
  %  the ability to construct the shannon graph for a record term.
  %  It also takes care of the variable indexing automatically (so
  %  one uses terms like all(x p(x)) with explicit variable names.
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

  %
  %  Utility procedure for transforming a FOF via an atom mapping function,
  %  i.e. a function that maps Atoms -> FOFs and can be pushed inside all
  %  logical operators.
  %
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

  proc {Theory_init SData PData}
    SData = state(fvBind: fvb
                  fvMode: _
                  skvNum: 0)
    PData = path(b: {Binding.init}
                pT: {TermSet.init}
                pF: {TermSet.init}
                qs: {QuantSet.init}
                polarity: _)
    {System.show init()}
  end

  proc {Theory_done _}
    {System.show done()}
  end

  proc {Theory_init_taut_a SData PData}
    {Theory_init SData PData}
    SData.fvMode = e
    PData.polarity = 0
  end

  proc {Theory_init_taut_e SData PData}
    {Theory_init SData PData}
    SData.fvMode = a
    PData.polarity = 0
  end

  proc {Theory_init_false_a SData PData}
    {Theory_init SData PData}
    SData.fvMode = e
    PData.polarity = 0
  end

  proc {Theory_init_false_e SData PData}
    {Theory_init SData PData}
    SData.fvMode = a
    PData.polarity = 0
  end

  proc {Theory_p_addNode P E SDIn#SDOut PDIn#PDOut Res}
    if E == 1 then
      PT2 = {TermSet.put P PDIn.pT}  Unifies in
      PDOut = {Record.adjoinAt PDIn pT PT2}
      Unifies = {TermSet.unify P PDIn.pF}
      if Unifies then Res=closed else Res=ok end
    else
      PF2 = {TermSet.put P PDIn.pF}  Unifies in
      PDOut = {Record.adjoinAt PDIn pF PF2}
      Unifies = {TermSet.unify P PDIn.pT}
      if Unifies then Res=closed else Res=ok end
    end
    SDIn = SDOut
  end

  proc {Theory_q_addNode Q E SDIn#SDOut PDIn#PDOut Res}
    QS2
  in
    if E == 1 then
      QS2 = {QuantSet.pushA PDIn.qs Q PDIn.b}
    else
      QS2 = {QuantSet.pushE PDIn.qs Q PDIn.b}
    end
    PDOut = {Record.adjoinAt PDIn qs QS2}
    SDIn = SDOut
    Res = ok
  end

  proc {Theory_eq_addNode T1 T2 E SDIn#SDOut PDIn#PDOut Res}
    Diffs
  in
    % We need to take care that we don't accidentally bind, or
    % assume a particular binding for, v_e terms.  Instead, we
    % assert constraints on their values for the path to be consistent.
    % These constraints should be periodically checked to ensure
    % it's still possible to give a value to that variable.
    % 
    % We proceed by finding all the places where the terms differ.
    % If one side of such a diff is a v_e term, we can put that in
    % the constraints.
    %
    Diffs = {LP.termDiffP T1 T2 Theory_eq_diffAtomic}
    if E == 1 then
        {Theory_eq_closeT Diffs SDIn#SDOut PDIn#PDOut Res}
    else EQOut in
        dis T1=T2 SDIn=SDOut PDIn=PDOut Res=closed
        [] not Diffs = nil end
           EQOut = {EQSet.addF PDIn.eqs {List.map Diffs StripVE}}
           if {EQSet.consistent EQOut} then
             PDOut = {Record.adjoinAt PDIn eqs EQOut}
             SDIn=SDOut Res=ok
           else
             PDOut=PDIn SDOut=SDIn Res=closed
           end
        end
    end
  end

  fun {Theory_eq_diffAtomic T}
    {IsFree T} orelse {Record.label T} == v_e
  end

  proc {Theory_eq_closeT Diffs SDIn#SDOut PDIn#PDOut Res}
    % We can close a true eq() node by asserting that any particular
    % pair from Diffs fails to unify. Alternately, we can assert that
    % they all unify and leave the path open.  Only one thing to watch
    % out for - we cannot assert non-unification on v_e terms.
    case Diffs of D1#D2|Ds then EQOut PDOut1 in
      case D1 of v_e(_ VE1) then VE2 in
        case D2 of v_e(_ VE2p) then VE2=VE2p
        else VE2 = D2 end
        EQOut = {EQSet.addT PDIn.eqs VE1#VE2}
        PDOut1 = {Record.adjoinAt PDIn eqs EQOut}
        {Theory_eq_closeT Ds SDIn#SDOut PDOut1#PDOut Res}
      else
        case D2 of v_e(_ VE2) then
          EQOut = {EQSet.addT PDIn.eqs D1#VE2}
          PDOut1 = {Record.adjoinAt PDIn eqs EQOut}
          {Theory_eq_closeT Ds SDIn#SDOut PDOut1#PDOut Res}
        else
          dis not D1=D2 end SDIn=SDOut PDIn=PDOut Res=closed
          []  D1=D2  {Theory_eq_closeT Ds SDIn#SDOut PDIn#PDOut Res}
          end
        end
      end
    else if {EQSet.consistent PDIn.eqs} then
           SDIn=SDOut PDIn=PDOut Res=ok
         else
           SDIn=SDOut PDIn=PDOut Res=closed
         end
    end
  end

  proc {StripVE TIn TOut}
    if {IsFree TIn} then TOut = TIn
    else
      case TIn of v_e(_ V) then TOut = V
      else
        TOut = {Record.map TIn StripVE}
      end
    end
  end

  proc {BindVE TIn Binding Mode TOut}
    if {IsFree} TIn then TOut=TIn
    else
      case TIn of v_e(Nm) then
        if {Not {Record.hasFeature Binding Nm}} then
          if Mode == a then Binding.Nm = v_e(Nm,_)
          else Binding.Nm = _ end
        end
        TOut = Binding.Nm
      else
        TOut = {Record.map TIn fun {$ T} {BindVE T Binding Mode} end}
      end
    end
  end

  proc {Theory_addNode K E SDIn#SDOut PDIn#PDOut Res}
    case K of p(P) then Pb Pe in
            % Transform the predicate into proving form.
            % First, apply the current bindings to bound vars.
            Pb = {Binding.bind PDIn.b P}
            % Then, bind e-vars according to operating mode.
            Pe = {BindVE Pb SDIn.fvBind SDIn.fvMode}
            % Strip v_e terms down to their representative variable
            % when sending them off for type constraints.
            {Lang.wff {StripVE Pe}}
            case Pe of eq(T1 T2) then
              {Theory_eq_addNode T1 T2 E SDIn#SDOut PDIn#PDOut Res}
            else
              {Theory_p_addNode Pe E SDIn#SDOut PDIn#PDOut Res}
            end
    []  q(Q) then
            {Theory_q_addNode Q E SDIn#SDOut PDIn#PDOut Res}
    else SDIn = SDOut PDIn = PDOut Res=ok
    end
    {System.show addNode(K E Res PDOut)}
  end

  proc {Theory_endPath L SDIn#SDOut PDIn#PDOut Res}
    % Don't bother closing nodes of opposite polarity, they're irrelevant
    if PDIn.polarity \= L then SDIn=SDOut PDIn=PDOut Res=ok
    % e-inconsistent paths can be immediately closed
    elseif {Not {Theory_e_consistent SDIn PDIn}} then
      skip
    else Qf Bf Sf in
      Sf = {QuantSet.popE PDIn.qs Qf Bf}
      if Qf == nil then Qt Bt St in
         St = {QuantSet.instA PDIn.qs Qt Bt}
         if Qt == nil then
           % Cant extend path and cant close it, can only fail
           {System.show endPath(L SDIn failed)}
           fail
         else
           % Extended by a positively quantified subgraph, only
           % 1-paths need to be considered.
           PDOut = {Record.adjoinList PDIn [qs#St b#Bt polarity#1]}
           Res = extend(Qt)
         end
         SDIn = SDOut
      else
         % Generate a new unique name for the introduced variable
         Bf = v_e(skv(SDIn.skvNum) _)|_
         SDOut = {Record.adjoinAt SDIn skvNum SDIn.skvNum+1}
         % Extended by a negatively quantified subgraph, only
         % 0-paths need to be considered.
         PDOut = {Record.adjoinList PDIn [qs#Sf b#Bf polarity#0]}
         Res = extend(Qf)
      end
    end
    {System.show endPath(L Res SDOut)}
  end


  %


  proc {Tautology_e F Binding Result}
    Binding = {Dictionary.new}
    case F of 1 then Result=yes
    [] 0 then Result=no
    else Result=unknown
    end
  end

  proc {Tautology_a F Res}
    Theory = th(init: Theory_init_taut_a
                addNode: Theory_addNode
                endPath: Theory_endPath
                done: Theory_done)
    ResP
  in
    ResP = {Search.base.one proc {$ R} {BDD.explore F Theory R} end}
    case ResP of [_] then Res=true
    else Res=false
    end
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
    Fs = [impl(and(impl(a b) impl(b c)) impl(a c))
          impl(and(impl(a b) impl(b c)) impl(d c))
          impl(all(x p(x)) p(a))
          impl(all(x p(x)) q(b))
          impl(p(a) exists(x p(x)))
          impl(exists(x p(x)) all(x p(x)))]
    Bs = [true false true false true false]
  in
    Lang = lang(wff: proc {$ P} skip end)
    for F in Fs B in Bs do local T P in
      P = {ParseRecord F}
      T = {Tautology_a P}
      {IsDet T true}
      B = T
    end end
  end

end

