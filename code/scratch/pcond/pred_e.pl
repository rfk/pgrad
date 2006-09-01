%
%  pred_e.pl:  logical reasoning using the E theorem prover
%
%  At this stage I havent found a way to utilise the notion of "axioms" -
%  perhaps I should convert them to clausal form or something.  Anyway,
%  the only really interesting interface predicate is entails/2.
%


fml2axioms(Fml,[Fml]).
add_to_axioms(Fml,Axs,[Fml|Axs]).
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
    % Universally quantiy all free variables in conc
    free_vars(Conc,ConcVars),
    ( ConcVars = [] ->
          Conc2 = Conc
    ;
          Conc2 = all(ConcVars,Conc)
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


e_cnf(Fml,Cnf) :-
    %tmp_file(e_in,InFile),
    %tmp_file(e_out,OutFile),
    InFile = 'in1.e',
    OutFile = 'out1.e',
    tell(InFile),
    write(fof(ax1,axiom,Fml)), write('.'),
    told,
    sformat(ECmd,'eprover --tstp-format --cnf --no-preprocessing -s ~w | grep -v "^#" > ~w',[InFile,OutFile]),
    shell(ECmd,_),
    see(OutFile),
    read(Cnf),
    seen.
    
