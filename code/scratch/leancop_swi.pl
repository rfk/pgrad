%% Version: 1.03  -  Date: 25/11/99  -  File: leancop_swi.pl
%%
%% Purpose: leanCoP: A Clausal Connection Prover for Classical Logic
%%
%% Author:  Jens Otten (jens@leancop.de)
%%
%% Usage:   prove(M).   % where M is a set of clauses
%%                      %  e.g. M=[[q(a)],[-p],[p, -q(X)]]
%%          prove(F).   % where F is a first-order formula
%%                      %  e.g. F=((p,all X:(p=>q(X)))=>all Y:q(Y))
%%                      %  (file nnf_mm.pl is needed)
%%
%% Web:     www.leancop.de


%%% prove matrix M / formula F

prove([C|M]) :- !, Time1 is cputime, prove([C|M],1),
                Time2 is cputime, Time is Time2-Time1, print(Time).

prove(F) :- Time1 is cputime, make_matrix(F,M), prove(M,1),
            Time2 is cputime, Time is Time2-Time1, print(Time).

prove(Mat,PathLim) :-
     append(MatA,[Cla|MatB],Mat), \+member(-_,Cla),
     append(MatA,MatB,Mat1),
     prove([!],[[-!|Cla]|Mat1],[],PathLim).

prove(Mat,PathLim) :-
     % Modified by rfk: set a maximum pathlimit of 10
     \+ground(Mat), PathLim < 10, PathLim1 is PathLim+1, prove(Mat,PathLim1).

prove([],_,_,_).

prove([Lit|Cla],Mat,Path,PathLim) :-
     (-NegLit=Lit;-Lit=NegLit) ->
        ( member(NegL,Path), unify_with_occurs_check(NegL,NegLit)
          ;
          append(MatA,[Cla1|MatB],Mat), copy_term(Cla1,Cla2),
          append(ClaA,[NegL|ClaB],Cla2),
          unify_with_occurs_check(NegL,NegLit),
          append(ClaA,ClaB,Cla3),
          ( Cla1==Cla2 ->
               append(MatB,MatA,Mat1)
               ;
               length(Path,K), K<PathLim,
               append(MatB,[Cla1|MatA],Mat1)
          ),
          prove(Cla3,Mat1,[Lit|Path],PathLim)
        ),
        prove(Cla,Mat,Path,PathLim).
