%
%  pred_e.pl:  logical reasoning using the E theorem prover
%
%  At this stage I havent found a way to utilise the notion of "axioms" -
%  perhaps I should convert them to clausal form or something.  Anyway,
%  the only really interesting interface predicate is entails/2.
%
%  We use E's quotes-identifiers-as-unique-objects convention to enforce
%  UNA on our domain objects.  To succssfully read formulae back from E,
%  the prolog flag 'double_quotes' must be set to 'atom'.
%


fml2axioms(Fml,Axs) :-
    ( is_list(Fml) ->
        Axs = Fml
    ;
        Axs = [Fml]
    ).
add_to_axioms(Fml,Axs,Axs2) :-
    ( is_list(Fml) ->
        append(Axs,Fml,Axs2)
    ;
        Axs2 = [Fml|Axs]
    ).
combine_axioms(Ax1,Ax2,Axs) :-
    append(Ax1,Ax2,Axs).
entails(Axs,Conc) :-
    copy_term(Conc,Conc2),
    eprove(Axs,Conc2,yes).

%%%  Guts of the implementation below this line %%%

eprove(Axioms,Conc,Result) :-
    % Create input/output files
    tmp_file(e_in,InFile),
    tmp_file(e_out,OutFile),
    tell(InFile),
    % Universally quantify all free variables in conc
    free_vars(Conc,ConcVars),
    ( ConcVars = [] ->
          Conc2 = Conc
    ;
          Conc2 = !(ConcVars : Conc)
    ),
    % Write out axioms
    e_write_axioms(Axioms,0,_), !,
    % Write out the conjecture
    write('fof(conj_1,conjecture,'),
    e_write(Conc2), write(').'), nl,
    told, !,
    % Call E and have it write its conclusions in output file
    sformat(ECmd,'eprover -xAuto -tAuto --memory-limit=512 --cpu-limit=5 --tstp-format -s ~w > ~w',[InFile,OutFile]),
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


e_write_cls([P]) :-
    e_write(P), !.
e_write_cls([P1,P2|Ps]) :-
    e_write(P1),
    write(' | '),
    e_write_cls([P2|Ps]).

e_write(Cls) :-
    is_list(Cls), !, Cls \= [],
    write('('),
    e_write_cls(Cls),
    write(')').
e_write(A=B) :-
    e_write_term(A),
    write('='),
    e_write_term(B), !.
e_write(A\=B) :-
    e_write_term(A),
    write('!='),
    e_write_term(B), !.
e_write(P) :-
    is_atom(P),
    P =.. [F|Terms],
    write(F),
    (Terms \= [] -> write('('), e_write_terms(Terms), write(')') ; true).
e_write(P & Q) :-
    write('('),
    e_write(P),
    write(' & '),
    e_write(Q),
    write(')').
e_write(P | Q) :-
    write('('),
    e_write(P),
    write(' | '),
    e_write(Q),
    write(')').
e_write(P => Q) :-
    write('('),
    e_write(P),
    write(' => '),
    e_write(Q),
    write(')').
e_write(P <=> Q) :-
    write('('),
    e_write(P),
    write(' <=> '),
    e_write(Q),
    write(')').
e_write(~P) :-
    write('~'),
    e_write(P).
e_write(!(V:P)) :-
    write('( ! '),
    write(V),
    write(' : ('),
    e_write(P),
    write('))').
e_write(?(V:P)) :-
    write('( ? '),
    write(V),
    write(' : ('),
    e_write(P),
    write('))').

e_write_terms([T]) :-
    e_write_term(T), !.
e_write_terms([T,T2|Ts]) :-
    e_write_term(T),
    write(','),
    e_write_terms([T2|Ts]).

e_write_term(T) :-
    var(T), !, write(T).
e_write_term(T) :-
    % We assume that any zero-arity functions are constants
    % and write them in double-quotes, to enforce UNA.
    ( functor(T,_,0) ->
        write('"'), write(T), write('"')
    ;
        T =.. [F|Args],
        write(F), write('('),
        e_write_terms(Args),
        write(')')
    ).
    

e_write_axioms([],N,N).
e_write_axioms([A|Axs],N,N2) :-
    N1 is N + 1,
    ( is_list(A) ->
        write('cnf(axiom'), write(N), write(',axiom,')
    ;
        write('fof(axiom'), write(N), write(',axiom,')
    ),
    e_write(A),
    write(').'), nl,
    e_write_axioms(Axs,N1,N2).


%
%  Convert the given formula to CNF
%
%  Unfortunately I cant seem to take advantage of E's CNF pre-processing,
%  as it throws away things it doesnt need for theorem proving but that I
%  need in the representation of the formula.  Maybe one day...
%

e_cnf(Fml,Cnf) :-
    tmp_file(e_in,InFile),
    tmp_file(e_out,OutFile),
    tell(InFile),
    write('fof(p1,plain,'),
    e_write(Fml),
    write(').'),
    told,
    e_readbility_pipeline(Pipes),
    %sformat(ECmd,'eprover --tstp-format --cnf --no-preprocessing -s ~w ~w > ~w',[InFile,Pipes,OutFile]),
    sformat(ECmd,'eprover --tstp-format --cnf -s ~w ~w > ~w',[InFile,Pipes,OutFile]),
    shell(ECmd,_),
    see(OutFile),
    e_read_clauses(Cnf1),
    e_fix_skolem(Cnf1,Cnf),
    seen.

%
%   Modify a file output by E so that it can be read back in as
%   prolog terms.
%   
e_readbility_pipeline(C) :-
    C = '| grep -v "^#" | sed -e \'s/!=/\\\\=/g\' '.

e_read_clauses(L) :-
    read(Cls),
    (Cls = end_of_file ->
        L = []
    ;
        Cls = cnf(_,_,F),
        flatten_op('|',[F],ClT),
        sort(ClT,Cl),
        L = [Cl|L2],
        e_read_clauses(L2)
    ).

%
%  Rename skolem variables from E form to skolem fluent form
%

e_fix_skolem(P,P1) :-
    is_atom(P),
    P =.. [F|Terms],
    e_fix_skolem_terms(Terms,Terms2),
    P1 =.. [F|Terms2].
e_fix_skolem([],[]).
e_fix_skolem([P|Ps],[Q|Qs]) :-
    e_fix_skolem(P,Q),
    e_fix_skolem(Ps,Qs).
e_fix_skolem(P & Q,P1 & Q1) :-
    e_fix_skolem(P,P1),
    e_fix_skolem(Q,Q1).
e_fix_skolem(P | Q,P1 | Q1) :-
    e_fix_skolem(P,P1),
    e_fix_skolem(Q,Q1).
e_fix_skolem(P => Q,P1 => Q1) :-
    e_fix_skolem(P,P1),
    e_fix_skolem(Q,Q1).
e_fix_skolem(P <=> Q,P1 <=> Q1) :-
    e_fix_skolem(P,P1),
    e_fix_skolem(Q,Q1).
e_fix_skolem(~P,~P1) :-
    e_fix_skolem(P,P1).
e_fix_skolem(!(V:P),!(V:P1)) :-
    e_fix_skolem(P,P1).
e_fix_skolem(?(V:P),?(V:P1)) :-
    e_fix_skolem(P,P1).

e_fix_skolem_terms([],[]).
e_fix_skolem_terms([T|Ts],[T2|Ts2]) :-
    % If it starts with "esk", it's an E skolem variable
    ( var(T) ->
        T2 = T
    ;
        T =.. [F|Args],
        ( sub_atom(F,0,3,_,esk) ->
            concat_atom([Id,Ar],'_',F),
            concat_atom([skol,Ar],SFName),
            T2 =.. [SFName,s0,Id|Args]
        ;
            T2 = T
        )
    ),
    e_fix_skolem_terms(Ts,Ts2).

