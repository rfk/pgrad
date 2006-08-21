%
%  pred_hugo.pl:  logical reasoning using the HeerHugo sat checker
%


fml2axioms(Fml,[Fml]).
add_to_axioms(Fml,Axs,[Fml|Axs]).
combine_axioms(Ax1,Ax2,Axs) :-
    append(Ax1,Ax2,Axs).
entails(Axs,Conc) :-
    copy_term(Conc,Conc2),
    hugo_prove(Axs,Conc2,yes).

%%%  Guts of the implementation below this line %%%

hugo_prove(Axioms,Conc,Result) :-
    % Create working directory and switch into it
    tmp_file(hugo_work,WorkDir),
    make_directory(WorkDir),
    working_directory(CWD,WorkDir),
    % Open input file for writing
    tell('Ain'),
    % Since it's a SAT checker, we use axioms & -conc
    hugo_write_list(Axioms),
    write('& ~('),
    hugo_write(Conc),
    write(')'),
    told,
    % actually run heerhugo
    shell('heerhugo',_),
    % Grep output file for "Inconsistent" indicating truth
    TCmd = 'grep "Inconsistent" Aout > /dev/null',
    ( shell(TCmd,0) ->
        Result = yes
    ;
      % Grep output file for "Satisfiable" indicating falsity
      FCmd = 'grep "Satisfiable" Aout > /dev/null',
      ( shell(FCmd,0) ->
          Result = no
      ;
          % Otherwise, we're none the wiser
          Result = unknown
      )
    ),
    % Switch back to previous working dir
    working_directory(_,CWD),
    working_directory(PWD,PWD), write('PWD: '), writeln(PWD).


hugo_write_list([]) :-
    write('(true)').
hugo_write_list([F|Fs]) :-
    write('('),
    hugo_write(F),
    write(') & '),
    hugo_write_list(Fs).

hugo_write(-Term) :-
    write('~('),
    hugo_write(Term),
    write(')'), !.
hugo_write(P -> Q) :-
    write('('),
    hugo_write(P),
    write(' -> '),
    hugo_write(Q),
    write(')'), !.
hugo_write(P <-> Q) :-
    write('('),
    hugo_write(P),
    write(' <-> '),
    hugo_write(Q),
    write(')'), !.
hugo_write(P & Q) :-
    write('('),
    hugo_write(P),
    write(' & '),
    hugo_write(Q),
    write(')'), !.
% Since there are no variables, we can enforce UNA directly in translation
hugo_write(P = Q) :-
    ( P=Q ->
        write(true)
    ;
        write(false)
    ).
hugo_write(P | Q) :-
    write('('),
    hugo_write(P),
    write(' | '),
    hugo_write(Q),
    write(')'), !.
hugo_write(all([],P)) :-
    hugo_write(P).
hugo_write(all([X:D|Vs],P)) :-
    % Instantiate variables with failure-driven-loop
    call(D,X),
    write('('),
    hugo_write(all(Vs,P)),
    write(') & '),
    fail
    ;
    write('true').
hugo_write(exists([],P)) :-
    hugo_write(P).
hugo_write(exists([X:D|Vs],P)) :-
    call(D,X),
    write('('),
    hugo_write(exists(Vs,P)),
    write(') | '),
    fail
    ;
    write('false').
hugo_write(P) :-
    is_literal(P),
    P =.. [F|Args],
    write(F),
    hugo_write_args(Args).

hugo_write_args([]).
hugo_write_args([H|T]) :-
    write('_'), write(H),
    hugo_write_args(T).

