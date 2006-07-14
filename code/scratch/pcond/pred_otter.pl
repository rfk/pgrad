%%
%%  from: http://www.id.cbs.dk/~mtk/logik/prolog/pred_otter.pro
%% 
%% Prolog interface to the Otter theorem prover and the Mace2 model builder
%%
%%     otter(+Axioms, -Result)
%%         <=> ask Otter/Mace2 to prove/disprove the consistency of Axioms;
%%             Result is instantiated to 'inconsistent' (=proven inconsistent
%%             by Otter), to a list of models found by Mace2 (=ie, the
%%             axioms are satisfiable and hence consistent), or to 'unknown'
%%             (=both Otter and Mace2 failed to find the answer). 
%%     otter(+Axioms, -Result, -InFile, -OtterLog, -Mace2Log)
%%         <=> like above, but return input file, Otter log, and Mace2 log
%%     otter_input(+Axioms, +InFile)
%%         <=> writes Otter-file InFile representing axioms.
%%     term2otter(+Term, -O)
%%         <=> Term can be represented as Otter formula O.
%%

%% Standard options to Otter and Mace2

:- flag(otter_options, _, '-t30').
:- flag(mace2_options, _, '-N20 -t30').

:- dynamic interpretation/2.

	otter(Axioms, Result) :-
		% Ask Otter
		otter(Axioms, Result, _InFile, _OtterLog, _Mace2Log).

	otter(Axioms, Result, InFile, OtterLog, Mace2Log) :-
		% Create file names
		tmp_file(in, InFile), 
		tmp_file(otter, OtterLog),
		tmp_file(mace2, Mace2Log),

		% Write axioms to InFile
		otter_input(Axioms, InFile),

		(	% Call Otter
			flag('otter_options', OtterOpt, OtterOpt),
			sformat(OtterCmd, 'otter ~w < ~w 2>&1 | tee ~w | grep PROOF > /dev/null', 
				[OtterOpt, InFile, OtterLog]),
			shell(OtterCmd, OtterStatus), 
			OtterStatus = 0, !,
			Result = 'inconsistent'; 

			% Call Mace2
			flag(mace2_options, Mace2Opt, Mace2Opt),
			sformat(Mace2CmdA, '(mace2 -P -c ~w 2>&1) < ~w > ~w', 
				[Mace2Opt, InFile, Mace2Log]),
			shell(Mace2CmdA, _),
			sformat(Mace2Cmd, '(mace2 -P ~w 2>&1) < ~w | tee -a ~w | grep "set is satisfiable" > /dev/null', 
				[Mace2Opt, InFile, Mace2Log]),
			shell(Mace2Cmd, Mace2Status), 
			Mace2Status = 0, !,
			models(Mace2Log, Result);

			% Otter and Mace2 failed to produce a result
			Result = 'unknown'
		).

%%     otter_input(+Axioms, +InFile)
%%         <=> writes Otter-file InFile representing axioms.

	otter_input(Axioms, InFile) :-
		tell(InFile),
		write_ln('set(auto).'),
		write_ln('formula_list(usable).'),

		% Write axioms
		member(Axiom, Axioms),
		term2otter(Axiom, O),
		format('    ~w.~n', [O]),
		fail;

		% Close file
		write_ln('end_of_list.'),
		told.

%% term2otter(+Term, -O)
%%     <=> Term can be represented as Otter formula O.

	% Unary operators
	term2otter(- Phi, O) :- !,
		term2otter(Phi, OPhi),
		sformat(O, '(- ~w)', [OPhi]).

	% Binary operators and =
	term2otter(Term, O) :- 
		Term =.. [Op, Phi, Psi],
		member(Op = OOp, [(&) = '&', (|) = '|', (->) = '->', 
			(<->) = '<->', (=) = '=', (\=) = '!=']), !,
		term2otter(Phi, OPhi),
		term2otter(Psi, OPsi),
		sformat(O, '(~w ~w ~w)', [OPhi, OOp, OPsi]).

	% Quantifiers
	term2otter(Term, O) :- 
		Term =.. [Quant, Var, Phi],
		member(Quant, [all, exists]),
		term2otter(Phi, OPhi),
		sformat(O, '(~w ~w (~w))', [Quant, Var, OPhi]).

	term2otter(Phi, O) :-
		predicate(Phi),
		Phi =.. [Pred|Args],
		(	% Proposition
			Args = [], !,
			O = Pred;

			% Predicate
			args2otter(Args, OArgs),
			sformat(O, '~w(~w)', [Pred, OArgs])
		).

	args2otter([H], H) :- !.
	args2otter([H|R], O) :- !,
		args2otter(R, OR),
		sformat(O, '~w, ~w', [H, OR]).

%% otter2pl(-File): store otter2pl Perl filter in temporary file File 
otter2pl(File) :-
	flag(otter2pl, File, File),
	atom(File), !.
otter2pl(File) :-
	tmp_file(otter2pl, File), 
	flag(otter2pl, _, File),
	tell(File),
	format('~w~n~w~n~w~n~w~n~w~n~w~n~w~n',
		['#!/usr/bin/perl',
		'my $prolog = 0;',
		'while (<>) {',
		'    $prolog = 0 if ($_ =~ /^end_of_model$/);',
		'    print $_ if ($prolog);',
		'    $prolog = 1 if ($_ =~ /^======================= Model #/);',
		'}']),
	told.

models(Mace2Log, _Models) :-
	% Filter Mace2Log
	tmp_file(models, File),
	otter2pl(Filter),
	sformat(Cmd, 'cat ~w | perl ~w > ~w', [Mace2Log, Filter, File]),
	shell(Cmd), 

	% Load model file
	load_files([File], [silent(1)]),
	fail.

models(_Mace2Log, Models) :-
	% Find models
	findall(Model, 
		(	retract(interpretation(N, Tables)),
			tables2model(N, Tables, Model)
		), ModelsUnsorted),
	sort(ModelsUnsorted, Models).

tables2model(N, Tables, Model) :-
	% Find all constants
	findall(Constant=Object, (
		member(function(Constant, [Object]), Tables),
		atomic(Constant)
		), Constants),
	
	% Find all predicates
	findall(Predicate = Tuples, (
		member(predicate(Template, Table), Tables),
		Template =.. [Predicate|Args],
		length(Args, Arity),
		findall(Tuple, (
			nth0(Pos, Table,  1),
			pos2tuple(N, Arity, Pos, Tuple)), Tuples)
		), Predicates),
	append(Constants, Predicates, Model).
	
pos2tuple(_N, 0, _Pos, []) :- !.
pos2tuple(N, Arity, Pos, Tuple) :-
	Digit is Pos mod N, 
	Pos1 is Pos // N,
	Arity1 is Arity - 1,
	pos2tuple(N, Arity1, Pos1, Tuple1),
	append(Tuple1, [Digit], Tuple), !.


