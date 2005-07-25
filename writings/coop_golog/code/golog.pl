%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% FILE: Main/golog.pl
%
% IndiGolog interpreter
%
% This version allows for search and rolling forward.
% For more information on Golog and some of its variants, see:
%     http://www.cs.toronto.edu/~cogrobo/
%
% WRITTEN BY: Maurice Pagnucco and Hector J. Levesque
% REVISED: June 15, 2000 
% TESTED: ECLiPSe 4.2.2 under RedHat Linux 6.2
%         ECLiPSe 5.0 under RedHat Linux 6.2
%         SWI Prolog 3.3.6 under RedHat Linux 6.2
%         LPA DOS-Prolog 3.83 under DOS on HP200LX
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%                             June 15, 2000
%
% This software was developed by the Cognitive Robotics Group under the
% direction of Hector Levesque and Ray Reiter.
%
%        Do not distribute without permission.
%        Include this notice in any copy made.
%
%
%         Copyright (c) 1992-2000 by The University of Toronto,
%                        Toronto, Ontario, Canada.
%
%                          All Rights Reserved
%
% Permission to use, copy, and modify, this software and its
% documentation for non-commercial research purpose is hereby granted
% without fee, provided that the above copyright notice appears in all
% copies and that both the copyright notice and this permission notice
% appear in supporting documentation, and that the name of The University
% of Toronto not be used in advertising or publicity pertaining to
% distribution of the software without specific, written prior
% permission.  The University of Toronto makes no representations about
% the suitability of this software for any purpose.  It is provided "as
% is" without express or implied warranty.
%
% THE UNIVERSITY OF TORONTO DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS
% SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
% FITNESS, IN NO EVENT SHALL THE UNIVERSITY OF TORONTO BE LIABLE FOR ANY
% SPECIAL, INDIRECT OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER
% RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF
% CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
% CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  In addition to a Golog program, users provide these predicates:
%
% -- prim_fluent(?Fluent): for each primitive fluent
% -- prim_action(?Action): for each primitive action
% -- exog_action(?Action): for each exogenous action
% -- senses(+Action, +Fluent): for each sensing action
% -- poss(+Action, +Condition): when Condition, Action is executable
% -- initially(+Fluent, +Value): Fluent has Value in S0, the initial situation
% -- causes_val(+Action, +Fluent, +Value, +Cond): when Cond holds, doing
%      Action causes fluent to have value
% -- proc(+Name, +Program): Golog complex action. It consists of a program
%      Name and a Program to be executed
% -- execute(+Action, +History, -SensingResult): do the Action, return
%      the SensingResult. The History is passed for diagnostic or other
%      use. The result is ignored unless action is a sensing action
% -- exog_occurs(-ActionList): return a list of exog_actions
%      that have occurred since the last time it was called
%      The predicate always succeeds returning [] when there are none
% -- initialize: run at start of programs
% -- finalize: run at end of programs
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% MAIN LOOP
%  The top level call is indigolog(E), where E is a program
%  The history H is a list of actions (prim or exog), initially []
%  Sensing reports are inserted as actions of the form e(fluent,value)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

indigolog(E) :- 
    initialize,
    reset_indigolog_dbs,
    indigo(E, []),
    finalize.

indigo(E, H) :-
    handle_exog(H, H1),
    handle_rolling(H1, H2), !, 
    (trans(E, H2, E1, H3) -> indigo2(H2, E1, H3) ;
        (final(E, H2) -> (nl, write('Success.'), nl) ;
                (nl, write('Program fails.'), nl))).

% indigo2(H, E1, H1), called only after a successful Trans

indigo2(H, E, H) :-
    indigo(E, H).   % The case of Trans for tests

indigo2(H, E, [stop_interrupts|H]) :- !,
    indigo(E, [stop_interrupts|H]).

indigo2(H, E, [wait|H]) :- !,
    pause_or_roll(H, H1), 
    handle_exog(H1, H2),
    (H1 = H2 -> indigo2(H1, E, [wait|H1]) ; indigo(E, H2)).

indigo2(H, E, [A|H]) :-
    \+ senses(A, _), !,
    execute(A, H, _),
    indigo(E, [A|H]).

indigo2(H, E, [A|H]) :-
    senses(A, F),
    execute(A, H, Sr),
    indigo(E, [e(F, Sr), A|H]).


%  Move initially(-, -) to currently(-, -) and clear exog actions

reset_indigolog_dbs :-
    retractall(indi_exog(_)),
    assert((indi_exog(_) :- fail)),
    retractall(currently(_, _)), 
    initially(F, V),
    assert(currently(F, V)),
    fail.

reset_indigolog_dbs.

indi_exog(_) :-
    fail.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  EXOGENOUS ACTIONS
%   Exogenous actions are stored in the local predicate indi_exog(Act)
%   until they are ready to be incorporated into the history
%   History H2 is H1 with all pending exog actions placed at the front
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

handle_exog(H1, H2) :- 
    save_exog,
    bagof(A, indi_exog(A), L),
    append(L, H1, H2), 
    retractall(indi_exog(_)),
    assert((indi_exog(_) :- fail)), !.

handle_exog(H1, H1).     % When there are no indi_exog clauses.

% Save all current exogenous events in the indi_exog predicate

save_exog :-
    exog_occurs(L) -> store_exog(L) ; true.

store_exog([]).
store_exog([A|L]) :-
    assertz(indi_exog(A)),
    store_exog(L).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  ROLL DATABASE FORWARD
%   Rolling forward means advancing the predicate currently(-,-) and
%   discarding the corresponding tail of the history.
%   There are 3 parameters specified by roll_parameters(L,N,M).
%       L: the history has to be longer than this, or don't bother
%       M: if the history is longer than this, forced roll
%       N: the length of the tail of the history to be preserved
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

roll_parameters(20, 40, 5).

can_roll(H) :-
    roll_parameters(L, _, _),
    length(H, L1),
    L1 > L.

must_roll(H) :-
    roll_parameters(_, M, _),
    length(H, L1),
    L1 > M.

pause_or_roll(H1, H2) :-
    can_roll(H1), !,
    roll_db(H1, H2).

pause_or_roll(H1, H1).

handle_rolling(H1, H2) :-
    must_roll(H1), !,
    roll_db(H1, H2).

handle_rolling(H1, H1).

roll_db(H1, H2) :-
    roll_parameters(_, _, N),
    split(N, H1, H2, H3),
    preserve(H3).

% split(N, H, H1, H2) succeeds if append(H1, H2, H) and length(H1) = N.

split(0, H, [], H).

split(N, [A|H], [A|H1], H2) :-
    N > 0,
    N1 is N - 1,
    split(N1, H, H1, H2).

% Move fluent values at H to temp(-, -) and then to currently(-, -)

preserve(H) :-
    write('Rolling down the river ... '),
    retractall(temp(_, _)), 
    prim_fluent(F),
    has_val(F, V, H),
    assert(temp(F, V)),
    fail.

preserve(_) :-
    retractall(currently(_, _)), 
    temp(F, V),
    assert(currently(F, V)),
    fail.

preserve(_) :-
    write('done'), nl, nl,
    save_exog. %  In case time is spent rolling.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TRANS and FINAL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ConGolog

final(iconc(_), _).

final(conc(E1, E2), H) :-
    final(E1, H),
    final(E2, H).

final(pconc(E1, E2), H) :-
    final(E1, H),
    final(E2, H).

trans(iconc(E), H, conc(E1, iconc(E)), H1) :-
    trans(E, H, E1, H1).

trans(conc(E1, E2), H, conc(E, E2), H1) :-
    trans(E1, H, E, H1).

trans(conc(E1, E2), H, conc(E1, E), H1) :-
    trans(E2, H, E, H1).

trans(pconc(E1, E2), H, E, H1) :- % bpconc(E1, E2, H) is for when E1 blocked at H
    trans(E1, H, E3, H1) ->
        E = pconc(E3, E2) ;
        trans(bpconc(E1, E2, H), H, E, H1).

trans(bpconc(E1, E2, H), H, E, H1) :- !,
    trans(E2, H, E3, H1),  % blocked history H
    (H1 = H -> E = bpconc(E1, E3, H) ; E = pconc(E1, E3)).

trans(bpconc(E1, E2, _), H, E, H1) :-
    trans(pconc(E1, E2), H, E, H1).

% Golog

final([], _).

final([E|L], H) :-
    final(E, H),
    final(L, H).

final(ndet(E1, E2), H) :-
    final(E1, H) ; final(E2, H).

final(if(P, E1, E2), H) :-
    holds(P, H) -> final(E1, H) ; final(E2, H).

final(star(_), _).

final(while(P, E), H) :-
    \+ holds(P, H) ; final(E, H).

final(pi(V, E), H) :-
    subv(V, _, E, E2), !,
    final(E2, H).

final(E, H) :-
    proc(E, E2), !,
    final(E2, H).

trans(wait, H, [], [wait|H]). % wait is a no-op but encourages rolling db

trans([E|L], H, E1, H2) :-
    \+ L = [],
    final(E, H),
    trans(L, H, E1, H2).

trans([E|L], H, [E1|L], H2) :-
    trans(E, H, E1, H2).

trans(?(P), H, [], H) :-
    holds(P, H).

trans(ndet(E1, E2), H, E, H1) :-
    trans(E1, H, E, H1) ; trans(E2, H, E, H1).

trans(if(P, E1, E2), H, E, H1) :-
    holds(P, H) -> trans(E1, H, E, H1) ; trans(E2, H, E, H1).

trans(star(E), H, [E1, star(E)], H1) :-
    trans(E, H, E1, H1).

trans(while(P, E), H, [E1, while(P, E)], H1) :-
    holds(P, H),
    trans(E, H, E1, H1).

trans(pi(V, E), H, E1, H1) :-
    subv(V, _, E, E2), !,
    trans(E2, H, E1, H1).

trans(E, H, E1, H1) :-
    proc(E, E2), !,
    trans(E2, H, E1, H1).

trans(E, H, [], [E|H]) :-
    prim_action(E),
    poss(E, P),
    holds(P, H).

% SEARCH (ignoring exogenous or other concurrent actions)

final(search(E), H) :-
    final(E, H).

trans(search(E), H, followpath(E1, L), H1) :-
    trans(E, H, E1, H1),
    findpath(E1, H1, L).

findpath(E, H, [E, H]) :-
    final(E, H).

findpath(E, H, [E, H|L]) :-
    trans(E, H, E1, H1),
    findpath(E1, H1, L).

final(followpath(E, [E, H]), H) :- !.

final(followpath(E, _), H) :-
    final(E, H).  % off path; check again

trans(followpath(E, [E, H, E1, H1|L]), H, followpath(E1, [E1, H1|L]), H1) :- !.

trans(followpath(E, _), H, E1, H1) :-
    trans(search(E), H, E1, H1).  % redo search

% INTERRUPTS

trans(interrupt(Trigger, Body), H, E1, H1) :-
   trans(while(interrupts_running, if(Trigger, Body, ?(neg(true)))), H, E1, H1).

trans(interrupt(V, Trigger, Body), H, E1, H1) :- 
    trans(while(interrupts_running, 
    pi(V, if(Trigger, Body, ?(neg(true))))), H, E1, H1).  

final(interrupt(Trigger, Body), H) :-
    final(while(interrupts_running, if(Trigger, Body, ?(neg(true)))), H).

final(interrupt(V, Trigger, Body), H) :- 
   final(while(interrupts_running,  pi(V, if(Trigger, Body, ?(neg(true))))), H).

trans(stop_interrupts, H, [], [stop_interrupts|H]).

final(stop_interrupts, _) :- fail.

holds(interrupts_running, H) :- !,
    \+ (H = [stop_interrupts|_]).

trans(prioritized_interrupts(L), H, E1, H1) :- 
    expand_interrupts(L, E), !,
    trans(E, H, E1, H1).

expand_interrupts([], stop_interrupts).

expand_interrupts([X|L], pconc(X, E)) :-
    expand_interrupts(L, E).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% HOLDS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

holds(and(P1, P2), H) :- !,
    holds(P1, H),
    holds(P2, H).

holds(or(P1, P2), H) :- !,
    (holds(P1, H) ; holds(P2, H)).

holds(neg(P), H) :- !,
    \+ holds(P, H).   % Negation by failure

holds(some(V, P), H) :- !,
    subv(V, _, P, P1),
    holds(P1, H).

holds(P, H) :-
    proc(P, P1), !,
    holds(P1, H).

holds(P, H) :-
    \+ proc(P, P1),
    subf(P, P1, H),
    call(P1).

% T2 is T1 with X1 replaced by X2

subv(_, _, T1, T2) :-
    var(T1), !,
    T2 = T1.

subv(X1, X2, T1, T2) :-
    T1 = X1, !,
    T2 = X2.

subv(X1, X2, T1, T2) :-
    T1 =..[F|L1],
    subvl(X1, X2, L1, L2),
    T2 =..[F|L2].

subvl(_, _, [], []).

subvl(X1, X2, [T1|L1], [T2|L2]) :-
    subv(X1, X2, T1, T2),
    subvl(X1, X2, L1, L2).

% P2 is P1 with all fluents replaced by their values at H

subf(P1, P2, _) :-
    var(P1), !,
    P2 = P1.

subf(P1, P2, H) :-
    P1 =..[F|L1],
    subfl(L1, L2, H),
    P3 =..[F|L2],
    subf2(P3, P2, H).

subf2(P3, P2, H) :-
    prim_fluent(P3),
    has_val(P3, P2, H).

subf2(P2, P2, _) :-
    \+ prim_fluent(P2).

subfl([], [], _).

subfl([T1|L1], [T2|L2], H) :-
    subf(T1, T2, H),
    subfl(L1, L2, H).

has_val(F, V, []) :-
    currently(F, V).

has_val(F, V, [Act|H]) :-
    sets_val(Act, F, V1, H) -> V = V1 ; has_val(F, V, H).

sets_val(Act, F, V, H) :-
    Act = e(F, V) ; (causes_val(Act, F, V, P), holds(P, H)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% EOF: Main/golog.pl
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
