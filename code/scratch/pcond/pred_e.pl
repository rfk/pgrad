%
%  pred_e.pl:  logical reasoning using the E theorem prover
%
%  At this stage I havent found a way to utilise the notion of "axioms" -
%  perhaps I should convert them to clausal form or something.  Anyway,
%  the only really interesting interface predicate is entails/2.
%
%  TODO: trying to enfore UNA using E's built-in functionality, we'll
%        see how I go...
%


fml2axioms(Fml,[Fml]).
add_to_axioms(Fml,Axs,[Fml|Axs]).
combine_axioms(Ax1,Ax2,Axs) :-
    append(Ax1,Ax2,Axs).
entails(Axs,Conc) :-
    copy_term(Conc,Conc2),
    eprove(Axs,Conc2,yes).

%%%  Guts of the implementation below this line %%%

vars_to_typed([],[]).
vars_to_typed([H|T],[H:_|T2]) :-
    vars_to_typed(T,T2).

eprove(Axioms,Conc,Result) :-
    % Create input/output files
    tmp_file(e_in,InFile),
    tmp_file(e_out,OutFile),
    tell(InFile),
    % Universally quantiy all free variables in conc
    free_vars(Conc,ConcVars),
    ( ConcVars = [] ->
          Conc2 = Conc
    ;
          vars_to_typed(ConcVars,ConcVars2),
          Conc2 = all(ConcVars2,Conc)
    ),
    % Write out axioms in TSTP format
    eprove_write_axioms(Axioms,0,_),
    % Write out the conjecture in TSTP format
    write_ln('fof(conj_1,conjecture,'),
    term2tstp_write(Conc2), nl,
    write_ln(').'),
    told,
    % Call E and have it write its conclusions in output file
    sformat(ECmd,'eprover -xAuto -tAuto --memory-limit=512 --cpu-limit --tstp-format -s ~w > ~w',[InFile,OutFile]),
    shell(ECmd,_),
    % Grep output file for "Proof found!" indicating truth
    sformat(TCmd,'grep "Proof found!" ~w > /dev/null',[OutFile]),
    ( shell(TCmd,0) ->
        Result = yes
    ;
      % Grep output file for "No proof found!" indicating falsity
      sformat(FCmd,'grep "No proof found!" ~w > /dev/null',[OutFile]),
      ( shell(FCmd,0) ->
          Result = no
      ;
          % Otherwise, we're none the wiser
          Result = unknown
      )
    ).


eprove_write_axioms([],N,N).
eprove_write_axioms([Ax|Axs],N0,N) :-
    write('fof(axiom_'), write(N0), write(',axiom,'), nl,
    term2tstp_write(Ax), nl,
    write(').'), nl,
    N1 is N0 + 1,
    eprove_write_axioms(Axs,N1,N).

term2tstp_write(P) :-
    var(P), write('V'), write(P), !.
term2tstp_write(-Term) :-
    write('~('),
    term2tstp_write(Term),
    write(')'), !.
term2tstp_write(P -> Q) :-
    write('('),
    term2tstp_write(P),
    write(' => '),
    term2tstp_write(Q),
    write(')'), !.
term2tstp_write(P <-> Q) :-
    write('('),
    term2tstp_write(P),
    write(' <=> '),
    term2tstp_write(Q),
    write(')'), !.
term2tstp_write(P & Q) :-
    write('('),
    term2tstp_write(P),
    write(' & '),
    term2tstp_write(Q),
    write(')'), !.
term2tstp_write(P = Q) :-
    write('('),
    term2tstp_write(P),
    write(' = '),
    term2tstp_write(Q),
    write(')'), !.
term2tstp_write(P | Q) :-
    write('('),
    term2tstp_write(P),
    write(' | '),
    term2tstp_write(Q),
    write(')'), !.
term2tstp_write(all(X,P)) :-
    write('( ! ['),
    term2tstp_write_vars(X),
    write('] : ('),
    term2tstp_write(P),
    write('))'), !.
term2tstp_write(exists(X,P)) :-
    write('( ? ['),
    term2tstp_write_vars(X),
    write('] : ('),
    term2tstp_write(P),
    write('))'), !.
term2tstp_write(P) :-
    % Enforce UNA by treating all atoms as unique object identifiers
    functor(P,P,0),
    write('"'), write(P), write('"'), !.
term2tstp_write(P) :-
    P =.. [F|Args],
    write(F),
    write('('),
    term2tstp_write_args(Args),
    write(')'), !.
term2tstp_write_args([H]) :-
    term2tstp_write(H).
term2tstp_write_args([H,H2|T]) :-
    term2tstp_write(H),
    write(','),
    term2tstp_write_args([H2|T]).

term2tstp_write_vars([]).
term2tstp_write_vars([V:_]) :-
    write('V'), write(V).
term2tstp_write_vars([V:_|T]) :-
    T \= [], write('V'), write(V), write(', '),
    term2tstp_write_vars(T).

