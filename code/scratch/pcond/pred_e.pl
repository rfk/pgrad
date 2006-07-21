%%
%% Prolog interface to the E theorem prover
%%


eprove(Axioms,Conc,Result) :-
    % Create input/output files
    tmp_file(e_in,InFile),
    tmp_file(e_out,OutFile),
    tell(InFile),
    % Write out axioms in TSTP format
    eprove_write_axioms(Axioms,0,_),
    % Write out the conjecture in TSTP format
    write_ln('fof(conj_1,conjecture,'),
    term2tstp_write(Conc), nl,
    write_ln(').'),
    told,
    % Call E and have it write its conclusions in output file
    sformat(ECmd,'eprover -xAuto -tAuto --memory-limit=256 --cpu-limit=60 --tstp-format -s ~w > ~w',[InFile,OutFile]),
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
    write('( ! [V'),
    write(X),
    write('] : ('),
    term2tstp_write(P),
    write('))'), !.
term2tstp_write(exists(X,P)) :-
    write('( ? [V'),
    write(X),
    write('] : ('),
    term2tstp_write(P),
    write('))'), !.
term2tstp_write(P) :-
    ground(P), write(P), !.
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

