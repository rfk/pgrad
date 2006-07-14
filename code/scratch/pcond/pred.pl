%% (c) 2004 by Matthias Trautner Kromann. 
%% Open-source software licensed under the GNU Public License.

%% This file implements various Prolog procedures for propositional
%% logic:
%%
%% 1. Syntax: Well-formed formulas
%% 
%%     wff(+Phi)
%%         <=>  Phi is a well-formed formula
%%     free_vars(Expression, Free)
%%         <=> The expression Expression contains the free variables
%%             listed in Free (in alphabetical order).
%%     proposition(Expression)
%%         <=> The expression Expression is a proposition, ie,
%%             contains no free variables.
%%
%% 2. Semantics: Interpretation in model
%%
%%     interpretation(+Model, +Assignment, +Phi, -Truth)
%%         <=> Proposition Phi has truth value Truth in model Model
%%             with variable assignment Assignment.
%%     interpretation_object(+Model, +Assignment, +ObjectTerm, -Entity)
%%         <=> the objectt term ObjectTerm has interpretation Entity
%%             in model Model with assignment function Assignment.
%%     domain(+Model, -Domain)
%%         <=> model Model has domain Domain.
%%     modify_assignment(Assignment, Var / Value, NewAssignment)
%%         <=> assignment function NewAssignment is the result of changing
%%             the assignment function Assignment by assigning
%%             value Value to variable Var.
%%
%% 3. Semantics: tautologies, consistency and satisfiability
%%     
%%     tautology(+Formula)
%%         <=> true iff Formula is a tautology
%%     counter_example(+Formula, -Model)
%%         <=> find one or more models in which Formula is false.
%%     otter(+Axioms, -Result)
%%         <=> ask Otter/Mace2 to prove/disprove the consistency of Axioms;
%%             Result is instantiated to 'inconsistent' (=proven inconsistent
%%             by Otter), to a list of models found by Mace2 (=ie, the
%%             axioms are satisfiable and hence consistent), or to 'unknown'
%%             (=both Otter and Mace2 failed to find an answer).
%%     otter(+Axioms, -Result, -InFile, -OtterLog, -Mace2Log)
%%         <=> like above, but return Otter input file, Otter log, and
%%             Mace2 log file names.
%%      
%% 4. Semantics: logical equivalence (<=>) and implication (=>)
%%
%%
%%     equivalent(+Phi, +Psi)  (or: Phi <=> Psi)
%%         <=> Phi and Psi are logically equivalent (or: Phi and Psi
%%             have the same truth value in all models)
%%     implies(+Phi, +Psi)     (or: Phi => Psi)
%%         <=> Phi logically implies Psi (or: Psi is a logical
%%             consequence of Phi, or: Phi implies Psi in all models)
%%
%%
%% 5. Semantics: logical arguments (inferences)
%%
%%     valid_inference(+Premises, +Conclusion)
%%         <=> the conjunction P1 /\.../\ Pn of the premises P1,...,Pn
%%             implies the conclusion.
%%     invalid_inference(+Premises, +Conclusion, -Model)
%%         <=> the conjunction P1 /\.../\ Pn of the premises P1,...,Pn
%%             does not imply the conclusion in model Model.




%% ---------------------------------------------------------------------- 
%% 1. Syntax: Well-formed formulas
%% ---------------------------------------------------------------------- 

%%
%% Define Prolog operator <-> (biimplication)
%%

	:- op(500, yfx, <->).
	:- op(500, yfx, &).

%%
%% Load Otter interface
%%

	:- [pred_otter].

%%
%% Well-formed formulas in propositional logic
%%
%%	wff(Phi) <=> Phi is a well-formed formula
%%

	wff(Phi) :-				% N-ary predicates
		predicate(Phi).
	wff(- Phi) :-				% Negations
		wff(Phi).
	wff(Phi & Psi) :-			% Conjunctions
		wff(Phi),
		wff(Psi).
	wff(Phi | Psi) :-			% Disjunctions
		wff(Phi),
		wff(Psi).
	wff(Phi -> Psi) :-			% Implications
		wff(Phi),
		wff(Psi).
	wff(Phi <-> Psi) :-			% Bi-implications
		wff(Phi),
		wff(Psi).
	wff(all(Var, Phi)) :-	% Universal quantification
		variable(Var),
		wff(Phi).
	wff(exists(Var, Phi)) :-	% Existential quantification
		variable(Var),
		wff(Phi).
	wff(Term1 = Term2) :-		% Equality
		(constant(Term1); variable(Term1)),
		(constant(Term2); variable(Term2)).
	wff(Term1 \= Term2) :-		% Inequality
		(constant(Term1); variable(Term1)),
		(constant(Term2); variable(Term2)).


	% Any atomic Prolog term is a valid constant
	constant(Constant) :-
		atomic(Constant),
		\+ variable(Constant).

	% A term T where T is an atomic Prolog term starting with x,y,z
	variable(Variable) :-
		atomic(Variable),
		name(Variable, [Char|_]),
		name('xyzuvw', VarChars),
		member(Char, VarChars), !.
	
	% Any Prolog atom that is not lower-case is a valid N-ary predicate name
	predicate(Phi) :- 
		Phi =.. [Pred|Args],

		% Check that predicate name is valid
		atomic(Pred),
		\+ member(Pred, [(-), (&), (|), (->), (<->), 
			all, exists, (=), (\=)]),
		
		% Check that arguments are valid constants or variables
		forall(member(Arg, Args), (
			constant(Arg);
			variable(Arg)
		)).

%%
%% Free variables
%%
%%		free_vars(Expression, Free)
%%			<=> The expression Expression contains the free variables
%%				listed in Free (in alphabetical order).
%%
	
	% Sort variables returned by free_vars_unsrt/1
	free_vars(Predicate, Free) :-
		free_vars_unsrt(Predicate, FreeUnsorted),
		msort(FreeUnsorted, Free).

	% Free variables in predicates and "="
	free_vars_unsrt(Predicate, Free) :-
		(predicate(Predicate); Predicate = (_ = _); Predicate = (_ \= _)), !,
		Predicate =.. [_|Args],
		findall(Arg, (member(Arg, Args), variable(Arg)), Free).

	% Free variables in negations
	free_vars_unsrt(- Expression, Free) :-
		free_vars(Expression, Free).

	% Free variables in expressions with binary logical operators
	free_vars_unsrt(Expression, Free) :-
		Expression =.. [Operator, Expr1, Expr2],
		member(Operator, [( & ), ( | ), ( -> ), ( <-> )]),
		free_vars(Expr1, Free1),
		free_vars(Expr2, Free2),
		union(Free1, Free2, Free).
	
	% Free variables in quantified expressions
	free_vars_unsrt(Expression, Free) :-
		Expression =.. [Quantifier, Var, Scope],
		member(Quantifier, [all, exists]),
		variable(Var),
		free_vars(Scope, FreeScope),
		subtract(FreeScope, [Var], Free).

%%
%% Propositions (formulas without unbound variables)
%%
%%		proposition(Expression)
%%			<=> the expression Expression is a proposition
%%

proposition(Expression) :-
	free_vars(Expression, []).


%% ----------------------------------------------------------------------
%% 2. Semantics: Interpretation in model
%% ----------------------------------------------------------------------

%% 	interpretation(Model, Assignment, Proposition, Value)
%%		<=> the proposition Proposition has interpretation Value
%%			in the model Model with assignment function Assignment.

	% Interpretation of variable
	interpretation_object(_Model, Assignment, Object, Value) :-
		member(Object = Value, Assignment), !.

	% Interpretation of constant
	interpretation_object(Model, _Assignment, Object, Value) :-
		member(Object = Value, Model),
		integer(Value), !.

	% Interpretation of predicate
	interpretation(Model, Assignment, Predicate, Truth) :-
		predicate(Predicate),
		Predicate =.. [P|Args],

		% Interpret arguments
		findall(O, (
			member(Arg, Args),
			once((
				interpretation_object(Model, Assignment, Arg, O);
				format('Error: unknown constant or variable ~w~n', [Arg]),
				O = '*'
			))), Tuple),

		% Find extension and determine whether tuple is contained in it
		member(P = Extension, Model),
		once((
			member(Tuple, Extension), !,
			Truth = 1;
			Truth = 0
		)).

	% Interpretation of negation
	interpretation(Model, Assignment, - Phi, Truth) :-
		interpretation(Model, Assignment, Phi, TruthNeg),
		(	% Negation is true
			TruthNeg = 1, !, Truth = 0;

			% Negation is false
			TruthNeg = 0, !, Truth = 1
		). 

	% Interpretation of conjunction
	interpretation(Model, Assignment, Phi & Psi, Truth) :-
		interpretation(Model, Assignment, Phi, TruthPhi),
		interpretation(Model, Assignment, Psi, TruthPsi),
		(	% Both Phi and Psi are true
			TruthPhi = 1, TruthPsi = 1, !, Truth = 1;

			% One of Phi or Psi is false
			(TruthPhi = 0; TruthPsi = 0), !, Truth = 0
		).
	
	% Interpretation of disjunction
	interpretation(Model, Assignment, Phi | Psi, Truth) :-
		interpretation(Model, Assignment, Phi, TruthPhi),
		interpretation(Model, Assignment, Psi, TruthPsi),
		(	% Phi or Psi is true
			(TruthPhi = 1; TruthPsi = 1), !, Truth = 1;

			% Both Phi and Psi are false
			TruthPhi = 0, TruthPsi = 0, !, Truth = 0
		).

	% Interpretation of implication
	interpretation(Model, Assignment, Phi -> Psi, Truth) :-
		interpretation(Model, Assignment, Phi, TruthPhi),
		interpretation(Model, Assignment, Psi, TruthPsi),
		(	% Psi is true or Phi is false
			(TruthPhi = 0; TruthPsi = 1), !, Truth = 1;

			% Phi is true and Psi is false
			TruthPhi = 1, TruthPsi = 0, !, Truth = 0
		).
				
	% Interpretation of bi-implication
	interpretation(Model, Assignment, Phi <-> Psi, Truth) :-
		interpretation(Model, Assignment, Phi, TruthPhi),
		interpretation(Model, Assignment, Psi, TruthPsi),
		(	% Phi and Psi are both true, or both false
			(	(TruthPhi = 0, TruthPsi = 0); 
				(TruthPhi = 1, TruthPsi = 1)), 
				!, Truth = 1;

			% Phi and Psi have different truth values
			(	(TruthPhi = 1, TruthPsi = 0); 
			 	(TruthPhi = 0, TruthPsi = 1)), 
				!, Truth = 0
		).

	% Interpretation of equality
	interpretation(Model, Assignment, X = Y, Truth) :-
		interpretation_object(Model, Assignment, X, OX),
		interpretation_object(Model, Assignment, Y, OY),
		OX = OY, !,
		Truth = 1;
		Truth = 0.

	% Interpretation of inequality
	interpretation(Model, Assignment, X \= Y, Truth) :-
		interpretation_object(Model, Assignment, X, OX),
		interpretation_object(Model, Assignment, Y, OY),
		OX \= OY, !,
		Truth = 1;
		Truth = 0.

	% Interpretation of universal quantification
	interpretation(Model, Assignment, all(Var, Phi), Truth) :-
		domain(Model, Domain),
		forall(member(D, Domain), (
			modify_assignment(Assignment, Var/D, NewAssignment),
			interpretation(Model, NewAssignment, Phi, 1)
		)), !,
		Truth = 1;
		Truth = 0.

	% Interpretation of existential quantification
	interpretation(Model, Assignment, exists(Var, Phi), Truth) :-
		domain(Model, Domain),
		member(D, Domain), 
		modify_assignment(Assignment, Var/D, NewAssignment),
		interpretation(Model, NewAssignment, Phi, 1), !,
		Truth = 1;
		Truth = 0.

% Find domain in model

	domain(Model, Domain) :-
		% Find all objects mentioned in Model
		findall(X, (
			% Domain objects referenced by constants
			member(_ = X, Model),
			atomic(X);

			% Domain objects in predicate extensions
			member(_ = Ext, Model),
			member(Tuple, Ext),
			member(X, Tuple),
			atomic(X)), Objects),

		% Remove duplicates
		sort(Objects, Domain).


% Modified assignment function g[x/d]

	modify_assignment(Assignment, Var/Value, NewAssignment) :-
		findall(X=Y, ((
			member(X=Y, Assignment),
			X \= Var
		)), Unchanged),
		sort([Var=Value|Unchanged], NewAssignment).
		

%% ----------------------------------------------------------------------
%% 3. Semantics: Tautologies, consistency, and satisfiability
%% ----------------------------------------------------------------------

	tautology(Formula) :-
		otter([- Formula], Answer),
		(	% Negated formula is inconsistent, ie, Formula is a tautology
			Answer = inconsistent, !;

			% Negated formula is consistent, ie, Formula is not a tautology
			is_list(Answer), !, fail;

			% We don't know
			format('warning: unable to determine whether ~w is a tautology', 
				[Formula]), fail
		).

	counter_example(Formula, Model) :-
		otter([ - Formula], Answer),
		(	% Counter-examples found 
			is_list(Answer), !,
			member(Model, Answer);

			% No counter-examples exist
			Answer = inconsistent, !,
			fail;

			% We don't know
			format('warning: unable to determine whether ~w is inconsistent', 
				[Formula]), fail
		).


%% ----------------------------------------------------------------------
%% 4. Semantics: logical equivalence <=> and implication =>
%% ----------------------------------------------------------------------

%%
%% Define the logical equivalence operator <=> in Prolog
%%

	:- op(800, yfx, <=>).
	:- op(800, yfx, =>).

%%
%%	equivalent(Phi, Psi)
%%		<=> Phi og Psi are logically equivalent

	equivalent(Phi, Psi) :-
		tautology(Phi <-> Psi).

	(Phi <=> Psi) :-
		equivalent(Phi, Psi).

%%
%% implies(Phi, Psi)
%%

	implies(Phi, Psi) :-
		tautology(Phi -> Psi).
	
	(Phi => Psi) :-
		implies(Phi, Psi).
	
%% ----------------------------------------------------------------------
%% 5. Semantics: logical arguments (inferences)
%% ----------------------------------------------------------------------

%% valid_inference(Premises, Conclusion)
%%		<=> the conjunction P1 /\.../\ Pn of the premises P1,...,Pn
%%			implies the conclusion.
%
%% invalid_inference(Premises, Conclusion, Model)
%%		<=> the conjunction P1 /\.../\ Pn of the premises P1,...,Pn
%%			does not imply the conclusion in Model.

	valid_inference(Premises, Conclusion) :-
		join(Premises, (&), Conjunction),
		Conjunction => Conclusion.
		
	invalid_inference(Premises, Conclusion, Model) :-
		join(Premises, (&), Conjunction),
		counter_example(Conjunction -> Conclusion, Model).
		
%%
%%	join(List, Operator, Term) 
%%		<=> the term Term is obtained by combining all the elements in
%%			List with the operator Operator.
%%

	join([X, Y], Operator, Term) :-
		Term =.. [Operator, X, Y], !.

	join([X|List], Operator, Term) :-
		join(List, Operator, ListTerm),
		Term =.. [Operator, X, ListTerm].

