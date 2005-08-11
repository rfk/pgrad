
%%
%%  MConGolog:  ConGolog for multiple agents
%%
%%  This is a proof-of-concept implementation of a ConGolog semantics
%%  for multiple agents.  While traditional ConGolog provides the
%%  ability to execute several high-level programs concurrently via
%%  interleaving of their primitive actions, it does not provide for
%%  the concurrent execution of primitive actions.  This is required in
%%  order to take advantage of the parallelism offered by multi-agent
%%  systems.
%%


%%  Termination Rules

final(nil,_).

final(seq(D1,D2),S) :-
    final(D1,S), final(D2,S).

final(choice(D1,D2),S) :-
    final(D1,S)
    ;
    final(D2,S).

final(pi(V,D),S) :-
    sub(V,_,D,Dr), final(Dr,S).

final(star(_),_).

final(if(Cond,D1,D2),S) :-
    holds(Cond,S), final(D1,S)
    ;
    holds(neg(Cond),S), final(D2,S).

final(while(Cond,D),S) :-
    holds(neg(Cond),S)
    ;
    final(D,S).

final(conc(D1,D2),S) :-
    final(D1,S), final(D2,S).

final(pconc(D1,D2),S) :-
    final(D1,S), final(D2,S).

final(cstar(_),_).

final(pcall(PArgs),S) :-
    sub(now,S,PArgs,PArgsS), proc(PArgsS,P), final(P,S).

%%  Transition Rules.

trans(C,S,Dp,Sp) :-
    sub(now,S,C,CS), to_cact(CS,CA), start(S,SStart),
    % TODO: Should a C containing LNTP actions be allowed after LNTP?
    % If there is a least-natural-time-point for S, then perhaps some
    % natural actions must occur first.  Otherwise, it is legal to do
    % the agent-initiated actions.
    ( lntp(S,LNTP) ->
      (
        % Get the list of LNTP actions
        findall(NA,(natural(NA),poss(NA,LNTP,S)),NActs),
        (
          % Can do them before the LNTP actions
          % This requires that no actions in the set are natural
          ( 
            \+ ( member(A,CA), natural(A) ),
            T .>=. SStart, T .<. LNTP, poss(CA,T,S),
            Sp = do(CA,T,S), Dp = nil
          )
          ;
          % Can do them at the same time
          ( 
            union(CA,NActs,CANat),
            poss(CANat,LNTP,S),
            Sp = do(CANat,LNTP,S), Dp = nil
          )
          ;
          % Can do the LNTP actions first, leaving program unaltered
          % TODO: this poss() call should always be true, right?
          ( 
            poss(NActs,LNTP,S),
            Sp = do(NActs,LNTP,S), Dp = C
          )
        )
      )
    ;
      poss(CA,T,S), Sp = do(CA,T,S), Dp = nil
    ).

trans(test(Cond),S,nil,S) :-
    holds(Cond,S).

trans(seq(D1,D2),S,Dp,Sp) :-
    trans(D1,S,D1r,Sp), Dp = seq(D1r,D2).
trans(seq(D1,D2),S,Dp,Sp) :-
    final(D1,S), trans(D2,S,Dp,Sp).

trans(choice(D1,D2),S,Dp,Sp) :-
    trans(D1,S,Dp,Sp) ; trans(D2,S,Dp,Sp).

trans(pi(V,D),S,Dp,Sp) :-
    sub(V,_,D,Dr), trans(Dr,S,Dp,Sp).

trans(star(D),S,Dp,Sp) :-
    Dp = seq(Dr,star(D)), trans(D,S,Dr,Sp).

trans(if(Cond,D1,D2),S,Dp,Sp) :-
    holds(Cond,S), trans(D1,S,Dp,Sp)
    ;
    holds(neg(Cond),S), trans(D2,S,Dp,Sp).

trans(while(Cond,D),S,Dp,Sp) :-
    Dp = seq(Dr,while(Cond,D)), holds(Cond,S), trans(D,S,Dr,Sp).

trans(conc(D1,D2),S,Dp,Sp) :-
    trans*(D1,S,Dr1,do(C1,T,S)),
    trans*(D2,S,Dr2,do(C2,T,S)),
    % TODO:  discuss best semantics for concurrent execution union
    %        For the moment, I'm going with a split between natural
    %        and agent-initiated actions.  Natural actions can be
    %        shared between concurrently execution programs, but
    %        agent-initiated actions cannot.
    \+ ( member(A,C1), member(A,C2), actor(A,_) ),
    union(C1,C2,CT), trans(CT,S,nil,Sp),
    Dp = conc(Dr1,Dr2)
    ;
    Dp = conc(Dr1,D2), trans(D1,S,Dr1,Sp)
    ;
    Dp = conc(D1,Dr2), trans(D2,S,Dr2,Sp).

trans(pconc(D1,D2),S,Dp,Sp) :-
    Dp = pconc(Dr1,D2), trans(D1,S,Dr1,Sp)
    ;
    Dp = pconc(D1,Dr2), trans(D2,S,Dr2,Sp), \+ trans(D1,S,_,_).

trans(cstar(D),S,Dp,Sp) :-
    Dp = conc(Dr,cstar(D)), trans(D,S,Dr,Sp).

trans(pcall(PArgs),S,Dr,Sr) :-
    sub(now,S,PArgs,PArgsS),
    proc(PArgsS,P), trans(P,S,Dr,Sr).


%%  Syntactic Sugar with Infix Operators

syn_sugar(D1 : D2,seq(D1,D2)).
syn_sugar(D1 / D2,choice(D1,D2)).
syn_sugar(D1 // D2,conc(D1,D2)).
syn_sugar(D1 >> D2,pconc(D1,D2)).
syn_sugar(?C,test(C)).
syn_sugar(Proc,pcall(Proc)) :-
    proc(Proc,_).

trans(D,S,Dp,Sp) :-
    syn_sugar(D,Ds),
    trans(Ds,S,Dp,Sp).
final(D,S) :-
    syn_sugar(D,Ds),
    final(Ds,S).


%%  Transitive Closure of Transition Rules

trans*(D,S,D,S).
trans*(D,S,Dp,Sp) :-
    trans(D,S,Dr,Sr),
    trans*(Dr,Sr,Dp,Sp).

%%  Definition of do()

do(D,S,Sp) :-
    % TODO:  prove that the semantics only generate legal situations,
    %        remove the need for legal(Sp).
    trans*(D,S,Dp,Sp),
    %nl, nl, display(Sp), nl, nl, display(Dp), nl, get_code(_),
    final(Dp,Sp),
    ( legal(Sp) ->
          show_action_history(Sp)
      ;
          display('ILLEGAL SITUATION PRODUCED!!')
    ).


show_action_history(s0) :-
    nl.
show_action_history(do(C,T,S)) :-
    show_action_history(S),
    display('do '), display(C), display(' at '), display(T), nl.


step(D,S,Dp,Sp) :-
    Sp = do(C,T,S), 
    trans*(D,S,Dp,Sp).


%%
%%  Execute the program in an on-line manner, i.e. no backtracking
%%  over the performance of actions.  Each action is performed at the
%%  minimum allowable time.
%%
%%  TODO: be clever here with a notion of 'current time' and perform
%%        each action at the current time or later...
%%
ol_do(D,S) :-
    ( step(D,S,Dr,Sr) ->
        Sr = do(C,T,S),
        ( inf(T,MinT) ->
            true
        ;
            start(S,SStart), MinT is SStart + 1
        ),
        display('do '), display(C), display(' at '), display(MinT), nl,
        ( final(Dr,Sr) ->
            display('SUCCEEDED!')
        ;
            ol_do(Dr,do(C,MinT,S))
        )
    ;
        display('FAILED!')
    ).



%%  Implementation of holds(Cond,Sit) predicate, with negation-as-failure

holds(and(C1,C2),S) :-
    holds(C1,S), holds(C2,S).
holds(or(C1,C2),S) :- 
    holds(C1,S)
    ;
    holds(C2,S).
holds(all(V,C),S) :-
    holds(neg(some(V,neg(C))),S).
holds(some(V,C),S) :-
    sub(V,_,C,Cr), holds(Cr,S).
holds(neg(neg(C)),S) :-
    holds(C,S).
holds(neg(and(C1,C2)),S) :-
    holds(or(neg(C1),neg(C2)),S).
holds(neg(or(C1,C2)),S) :-
    holds(and(neg(C1),neg(C2)),S).
holds(neg(all(V,C)),S) :-
    holds(some(V,neg(C)),S).
holds(neg(some(V,C)),S) :-
    \+ holds(some(V,C),S).
holds(P_Xs,S) :-
    P_Xs \= and(_,_), P_Xs \= or(_,_), P_Xs \= neg(_), P_Xs \= all(_,_),
    P_Xs \= some(_,_), sub(now,S,P_Xs,P_XsS), P_XsS.
holds(neg(P_Xs),S) :-
    P_Xs \= and(_,_), P_Xs \= or(_,_), P_Xs \= neg(_), P_Xs \= all(_,_),
    P_Xs \= some(_,_), sub(now,S,P_Xs,P_XsS), \+ P_XsS.
    

%%  Substitution of terms

sub(_,_,T,Tr) :-
    var(T), Tr = T.
sub(X,Y,T,Tr) :-
    \+ var(T), T = X, Tr = Y.
sub(X,Y,T,Tr) :-
    T \= X, T =.. [F|Ts], sub_list(X,Y,Ts,Trs), Tr =.. [F|Trs].

sub_list(_,_,[],[]).
sub_list(X,Y,[T|Ts],[Tr|Trs]) :-
    sub(X,Y,T,Tr), sub_list(X,Y,Ts,Trs).

