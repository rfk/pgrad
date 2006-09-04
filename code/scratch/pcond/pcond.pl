
%
%  pcond_d1(F,C,P1)  -  depth 1 persistence condition for fluent F
%
%    The basic meaning of this pedicate is: if fluent F holds in situation
%    s, then it will continue to hold in all C-successors of s as long
%    as P1 is true in s.
%

pcond_d1(F,C,P1) :-
    ( bagof(Cn,pcond_d1_bagof(F,C,Cn),Cns) ->
        joinlist((&),Cns,P1tmp),
        simplify_c(P1tmp,P1)
    ;
        P1=true
    ).

pcond_d1_bagof(F,C,Cn) :-
    action_with_vars(A,Vs),
    regression(F,A,R),
    adp_fluent(C,A,Ec),
    Cnt = !(Vs : (R | ~Ec)),
    simplify_c(Cnt,Cn).

%
%  pcond(F,C,P)  -  persistence condition for F under C
%

pcond(F,C,P) :-
    fml2cnf(F,Cnf),
    pcond_cnf([],Cnf,C,Pc),
    cnf2fml(Pc,P).


pcond_cnf(P,[],_,P).
pcond_cnf(Pt,[Cl|Cls],C,P) :-
    length(Pt,LPt), length([Cl|Cls],LCl),
    write('Length: '), writeln(LPt : LCl),
    ( pcond_cnf_entails(Pt,Cl) ->
        pcond_cnf(Pt,Cls,C,P)
    ;
        joinlist('|',Cl,F),
        pcond_d1(F,C,F1),
        fml2cnf(F1,Cnf1),
        append(Cls,Cnf1,NewCls),
        pcond_cnf([Cl|Pt],NewCls,C,P)
    ).

pcond_cnf_entails(Cls,Cl) :-
    domain_axioms(Axs),
    add_to_axioms(Cls,Axs,Axs2),
    joinlist('|',Cl,Fl),
    entails(Axs2,Fl).

