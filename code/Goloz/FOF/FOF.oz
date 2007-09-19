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
%     FOF.lang.assign:  a procedure taking a list of free variables, and
%                       assigning them to terms from the domain.  This is
%                       used as a final check of whether a particular set
%                       of constraints is consistent.
%
%  This is done using a free variable rather than e.g. a cell because it
%  affects memoization and other features of the module.  Each consumer of
%  this module should use {Module.link} to create their own private
%  copy.
%

functor 

import

  LP at '../LP.ozf'
  Memo at '../Memo/Memo.ozf'
  BDD
  Binding
  TermSet
  QuantSet
  EQSet
  VarMap

  Search
  Space
  Property
  System

export

  ParseRecord
  Transform
  Transformation
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
  ToRecord

  Test

define

  {Property.put 'print.width' 10000}
  {Property.put 'print.depth' 10000}

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
  %              constrain the values taken by the variable.  This setup
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

  fun {Ite C F1 F2}
    {BDD.replaceLeaves C F1 F2}
  end

  fun {All F}
    {BDD.bdd q(F) 1 0}
  end

  fun {Exists F}
    {BDD.bdd q({Neg F}) 0 1}
  end

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
  %  If the record contains free variables, these will be replaced with
  %  v_e(Nm) terms.  VM is returned as a VarMap giving the correspondance
  %  between variables and their names.
  %

  proc {ParseRecord Rec VM F}
    VM = {VarMap.new}
    {ParseRecordB Rec {Binding.init} VM F}
  end

  proc {ParseRecordB Rec B VM F}
    case Rec of true then F = 1
    []   false then F = 0
    []   and(...) then case {Record.toList Rec} of nil then F = 1
                        [] H|Ts then HF = {ParseRecordB H B VM}
                                   M = proc {$ Q G} {ParseRecordB Q B VM G} end
                                   TFs = {List.map Ts M}
                                  in
                                   F = {List.foldL TFs Conj HF}
                        end
    []   'or'(...) then case {Record.toList Rec} of nil then F = 0
                        [] H|Ts then HF = {ParseRecordB H B VM}
                                   M = proc {$ Q G} {ParseRecordB Q B VM G} end
                                   TFs = {List.map Ts M}
                                  in
                                   F = {List.foldL TFs Disj HF}
                        end
    []   neg(R) then F = {Neg {ParseRecordB R B VM}}
    []   impl(R1 R2) then F={Impl {ParseRecordB R1 B VM} {ParseRecordB R2 B VM}}
    []   equiv(R1 R2) then F={Equiv {ParseRecordB R1 B VM} {ParseRecordB R2 B VM}}
    []   ite(C R1 R2) then F={Ite {ParseRecordB C B VM} {ParseRecordB R1 B VM} {ParseRecordB R2 B VM}}
    []   all(Nm R) then F = {All {ParseRecordB R {Binding.push B Nm} VM}}
    []   exists(Nm R) then F={Exists {ParseRecordB R {Binding.push B Nm} VM}}
    []   nall(Nm R) then F = {Exists {ParseRecordB neg(R) {Binding.push B Nm} VM}}
    []   nexists(Nm R) then F={All {ParseRecordB neg(R) {Binding.push B Nm} VM}}
    else F = {Atom {Binding.unbind B {VarMap.map VM Rec}}}
    end
  end


  proc {ToRecord Fml Rec}
    ITE = {BDD.deref Fml} in
    case ITE of ite(K T F) then Rec = ite(K {ToRecord T} {ToRecord F})
    [] 1 then Rec = true
    else Rec = false
    end
  end

  %
  %  Utility procedure for transforming a FOF via an atom mapping function,
  %  i.e. a function that maps Atoms -> FOFs and can be pushed inside all
  %  logical operators.
  %
  %  ProcP:  procedure to transform a single atom
  %  ProcR:  recursive call to transform an entire FOF
  %  Args:   additional arguments to the transformation
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
  %  Produce a function that will transform a FOF by calling
  %  the given procedure Proc on each kernel.
  %
  proc {Transformation FName Proc Trans}
   M_Trans R_Trans R_Proc
  in
    case {Procedure.arity Proc} of 2 then
          proc {Trans F T}
            {Memo.memoCall FName M_Trans [F] T}
          end
          proc {M_Trans Args T}
            [F] = Args
          in
            {Transform R_Proc R_Trans nil F T}
          end
          proc {R_Proc F _ T}
            {Proc F T}
          end
          proc {R_Trans F _ T}
            {Trans F T}
          end
    []  3 then
          proc {Trans F A T}
            {Memo.memoCall FName M_Trans [F A] T}
          end
          proc {M_Trans Args T}
            [F A] = Args
          in
            {Transform Proc R_Trans A F T}
          end
          proc {R_Trans F A T}
            {Trans F A T}
          end
    else fail
    end
  end

  %
  %  Strip free variable terms v_e(Nm V) from a record, leaving in
  %  their place just the Oz variable V.  This is useful for handing
  %  the terms off to the outside world for e.g. checking consistency.
  %
  proc {StripVE TIn TOut}
    if {IsFree TIn} then TOut = TIn
    elseif {Not {Record.is TIn}} then TOut = TIn
    else
      case TIn of v_e(_ V) then TOut = V
      else
        TOut = {Record.map TIn StripVE}
      end
    end
  end

  %
  %  Bind free-variable terms v_e(Nm) in a record, according to how they
  %  are to be dealth with.  If Mode is 'a' then we're interested in all
  %  possible assignments to these variables, so they should be replaced
  %  with v_e(Nm V) for internal theorem-proving purposes.  If Mode is 'e'
  %  then we're only interested in finding one particular assignment to
  %  these variables, so just replace them with free vars.
  %
  %  Binding is a dictionary mapping names to bindings, which is updated
  %  as new names are discovered. This is done thread-safely.
  %
  proc {BindVE TIn Mode Binding TOut}
    if {IsFree TIn} then TOut=TIn
    elseif {Not {Record.is TIn}} then TOut=TIn
    else
      case TIn of v_e(Nm) then OldB NewB in
        {Dictionary.condExchange Binding Nm nil OldB NewB}
        if {IsFree OldB} orelse OldB \= nil then
            TOut = OldB  NewB = OldB
        else
          if Mode == a then NewB = v_e(Nm _)
          else NewB = _ end
          TOut = NewB
        end
      else
        TOut = {Record.map TIn fun {$ T} {BindVE T Mode Binding} end}
      end
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
    SData = state(fvBind: {Dictionary.new}
                  fvMode: _
                  skvNum: 0
                  aVars: nil)
    PData = path(b: {Binding.init}
                pT: {TermSet.init}
                pF: {TermSet.init}
                qs: {QuantSet.init}
                eqs: {EQSet.init}
                eVars: nil
                polarity: _)
  end

  %
  %  Called when exploration is complete.  Finds a consitent set of
  %  bindings for all a-quantified variables, to make sure we haven't
  %  stuffed up.
  %
  proc {Theory_done SData Outcome Res}
    {Lang.assign SData.aVars}
    Res = SData
  end

  proc {Theory_init_taut_a SData PData}
    {Theory_init SData PData}
    SData.fvMode = a
    PData.polarity = 0
  end

  proc {Theory_init_taut_e SData PData}
    {Theory_init SData PData}
    SData.fvMode = e
    PData.polarity = 0
  end

  proc {Theory_init_false_a SData PData}
    {Theory_init SData PData}
    SData.fvMode = a
    PData.polarity = 1
  end

  proc {Theory_init_false_e SData PData}
    {Theory_init SData PData}
    SData.fvMode = e
    PData.polarity = 1
  end

  %
  %  Add a generic predicate to the current path.
  %  P is the predicate term, E indicates the edge it was traversed through.
  %
  proc {Theory_addPred P E SDIn#SDOut PDIn#PDOut Res}
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

  %
  %  Add a quantified sub-graph to the current path.
  %  Q is the sub-graph, E indicates the edge it was traversed through.
  %
  proc {Theory_addQuant Q E SDIn#SDOut PDIn#PDOut Res}
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

  %
  %  Add an equality to the current path.
  %  T1 and T2 are the terms to be made equal. E gives the
  %  edge through which it was traversed.
  %
  proc {Theory_addEq T1 T2 E SDIn#SDOut PDIn#PDOut Res}
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
    {IsFree T} orelse {Not {Record.is T}} orelse {Record.label T} == v_e
  end

  proc {IsEVar V B}
    if {IsFree V} then B = false
    else
      case V of v_e(...) then B = true
      else B = false end
    end
  end

  %
  %  Attempt to close a path that has just had a true eq-node added.
  %  This can be done by asserting that any particular pair from the
  %  Diffs list fails to unify.  Alternately, we can assert that they
  %  all unify and leave the path open.
  %
  %  The only complication is v_e terms, which we can only insert
  %  into the list of path constraints.
  %
  proc {Theory_eq_closeT Diffs SDIn#SDOut PDIn#PDOut Res}
    case Diffs of D1#D2|Ds then EQOut PDOut1 V1 V2 in
      if {IsEVar D1} then VE1 VE2 in
        D1 = v_e(_ VE1)
        if {IsEVar D2} then D2 = v_e(_ VE2)
        else VE2 = D2 end
        EQOut = {EQSet.addT PDIn.eqs VE1#VE2}
        PDOut1 = {Record.adjoinAt PDIn eqs EQOut}
        {Theory_eq_closeT Ds SDIn#SDOut PDOut1#PDOut Res}
      else
        if {IsEVar D2} then VE2 in
          D2 = v_e(_ VE2)
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

  %
  %  Prove that there's a consistent assignment to all e-vars on
  %  the current path.  We use Lang.assign to ensure that there is one.
  %
  proc {Theory_eq_consistent SData PData B}
    EVars Check S
  in
    if SData.fvMode == e then
      EVars = {List.append PData.eVars
                           {List.map {Dictionary.items SData.fvBind} StripVE}}
    else
       EVars = PData.eVars
    end
    proc {Check _}
      {EQSet.assert PData.eqs}
      {Lang.assign EVars}
    end
    S = {Space.new Check}
    case {Space.askVerbose S} of failed then B = false
    else B = true end
  end

  %
  %  Add the given kernel to the current path.
  %
  proc {Theory_addNode K E SDIn#SDOut PDIn#PDOut Res}
    case K of p(P) then Pb Pe in
            % Transform the predicate into proving form.
            % First, apply the current bindings to bound vars.
            Pb = {Binding.bind PDIn.b P}
            % Then, bind e-vars according to operating mode.
            Pe = {BindVE Pb SDIn.fvMode SDIn.fvBind}
            % Strip v_e terms down to their representative variable
            % when sending them off for type constraints.
            {Lang.wff {StripVE Pe}}
            case Pe of eq(T1 T2) then
              {Theory_addEq T1 T2 E SDIn#SDOut PDIn#PDOut Res}
            else
              {Theory_addPred Pe E SDIn#SDOut PDIn#PDOut Res}
            end
    []  q(Q) then
            {Theory_addQuant Q E SDIn#SDOut PDIn#PDOut Res}
    else SDIn = SDOut PDIn = PDOut Res=ok
    end
  end

  %
  %  Attempt to end the current path at the given leaf.
  %
  proc {Theory_endPath L SDIn#SDOut PDIn#PDOut Res}
    if PDIn.polarity \= L then
      % Don't bother closing nodes of opposite polarity, they're irrelevant
      SDIn=SDOut PDIn=PDOut Res=ok
    elseif {Not {Theory_eq_consistent SDIn PDIn}} then
      % e-inconsistent paths can be immediately closed
      SDIn=SDOut SDIn=PDOut Res=closed
    else Qf Bf Sf in
      % Otherwise, we can extend the paths by quantified subgraphs.
      % Apply e-quants before a-quants since they get used up.
      Sf = {QuantSet.popE PDIn.qs Qf Bf}
      if Qf == nil then Qt Bt St in
         St = {QuantSet.instA PDIn.qs Qt Bt}
         if Qt == nil then
           % Cant extend path and cant close it, can only fail
           fail
         else NewVar in
           % Extended by a positively quantified subgraph, only
           % 1-paths need to be considered.
           Bt = NewVar|_
           SDOut = {Record.adjoinAt SDIn aVars NewVar|SDIn.aVars}
           PDOut = {Record.adjoinList PDIn [qs#St b#Bt polarity#1]}
           Res = extend(Qt)
         end
      else
         % Generate a new unique name for the introduced variable
         Bf = v_e(skv(SDIn.skvNum) _)|_
         SDOut = {Record.adjoinAt SDIn skvNum (SDIn.skvNum+1)}
         % Extended by a negatively quantified subgraph, only
         % 0-paths need to be considered.
         PDOut = {Record.adjoinList PDIn [qs#Sf b#Bf polarity#0
                                          eVars#(Bf.1.2|PDIn.eVars)]}
         Res = extend(Qf)
      end
    end
  end


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  proc {Explore F Init Searcher}
    Theory = th(init: Init
                addNode: Theory_addNode
                endPath: Theory_endPath
                done: Theory_done)
  in
    Searcher = {New Search.object script(proc {$ R} {BDD.explore F Theory R} end)}
  end

  %
  %  Determine whether some binding of the free variables make F tautology.
  %  Returns either nil (not a tautology) or a record mapping variable
  %  names to values.
  %
  proc {Tautology_e F Binding}
    Searcher = {Explore F Theory_init_taut_e}
  in
    {YieldNextBinding Searcher Binding}
  end

  proc {YieldNextBinding Searcher Binding}
    SDOut
  in
    SDOut = {Searcher next($)}
    if SDOut == nil then Binding = nil
    else
     choice
        Binding = {Dictionary.toRecord b SDOut.1.fvBind}
     [] {YieldNextBinding Searcher Binding}
     end
    end
  end

  %
  %  Determine whether F is a tautology for all possible bindings of
  %  the free variables.  Returns a Bool.
  %
  proc {Tautology_a F Res}
    Searcher = {Explore F Theory_init_taut_a}
    SDOut = {Searcher next($)}
  in
    if SDOut == nil then Res = false
    else Res = true end
  end

  %
  %  Like Tautology_e, but checking falsehood.
  %
  proc {Falsehood_e F Binding}
    Searcher = {Explore F Theory_init_false_e}
  in
    {YieldNextBinding Searcher Binding}
  end

  %
  %  Like Tautology_a, but checking falsehood.
  %
  proc {Falsehood_a F Res}
    Searcher = {Explore F Theory_init_false_a}
    SDOut = {Searcher next($)}
  in
    if SDOut == nil then Res = false
    else Res = true end
  end


  proc {Test}
    {Test_vars}
    {Test_prover}
  end

  proc {Test_vars}
    B1 = {Dictionary.new}
    B2 = {Dictionary.new}
    VM = {VarMap.new}
    V1 V2
    T1 T2 T3 T4
  in
    {BindVE p(a b) a B1 p(a b)}
    {BindVE p(a b) e B1 p(a b)}
    {BindVE p(a v_e(test)) a B1 p(a v_e(test T1))}
    {IsFree T1 true}
    {BindVE p(a v_e(test)) e B1 p(a v_e(test T1))}
    {IsFree T1 true}
    {BindVE p(a v_e(test)) e B2 p(a T2)}
    {IsFree T2 true}
    {BindVE {VarMap.map VM p(a V1)} a B2 p(a v_e(_ T3))}
    {IsFree T3 true}
    {BindVE {VarMap.map VM p(a V2)} e B2 p(a T4)}
    {IsFree T4 true}
  end

  proc {Test_prover}
    V1
    Fs = [impl(and(impl(a b) impl(b c)) impl(a c))
          impl(and(impl(a b) impl(b c)) impl(d c))
          impl(all(x p(x)) p(a))
          impl(all(x p(x)) q(b))
          impl(p(a) exists(x p(x)))
          impl(exists(x p(x)) all(x p(x)))
          all(x all(y impl(eq(x y) eq(y x))))
          all(a all(b all(c impl(and(eq(a b) eq(b c)) eq(c a)))))
          all(a all(b all(c impl(eq(a b) eq(c b)))))
          impl(p(a) p(_))
          ite(eq(thomas thomas) ite(eq(V1 knife(1)) true false) false)]
    Be = [true false true false true false true true false true true]
    Ba = [true false true false true false true true false false false]
  in
    {List.length Fs} = {List.length Be}
    {List.length Fs} = {List.length Ba}
    Lang = lang(wff: proc {$ _} skip end
                assign: proc {$ _} skip end)
    for F in Fs B in Be do local T P VM BM in
      P = {ParseRecord F VM}
      BM = {Search.base.one proc {$ R} {Tautology_e P R} end}.1
      T = (BM \= nil)
      {IsDet T true}
      if B == T then skip else raise F end end
    end end
    for F in Fs B in Ba do local T P VM BM in
      P = {ParseRecord F VM}
      T = {Tautology_a P}
      {IsDet T true}
      if B == T then skip else raise F end end
    end end
  end

end

