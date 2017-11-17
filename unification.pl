/*=====================================================
                       Unification
=====================================================*/ 

:- style_check(-discontiguous).
 
%%% unify_all_open(N, Closed, Open, Goal, FinalBottom-FinalProof-FinalLinks)
%%% ============================================================
%%%
%%%     N      ==> Index to prevent spurious ambiguity, and adds efficiency
%%%     Closed ==> List of closed unfolds
%%%     Open   ==> List of open unfolds
%%%     Goal   ==> The unfolded goal formula. Only added when 
%%%                there is just one closed or open unfold left.
%%%
%%%     FinalBottom-FinalProof-FinalLinks
%%%            <== Tuple of the completely unified proof, 
%%%                final bottomsequent and list of axiom links.

% Case for atomic axioms like np |- np.
unify_all_open(_, [], [], vdash(0,0-A-n,0-B-n)-FProof-GHoles, Links, vdash(0,0-A-n,0-B-n)-FProof-FLinks) :-
    focus_shift(vdash(0,0-A-n,0-B-n)-FProof-GHoles, Links, FLinks).

% The cases when there isn't one unfolded goal, but two lists as input/output.
unify_all_open(_, [CBottom-CProof], [], [], FLinks, vdash(0,0-A-n,0-B-n)-FProof-FLinks) :-   
    residuate(CBottom-CProof, vdash(0,0-A-n,0-B-n)-FProof).
    
unify_all_open(_, [], [Bottom-Proof-OHoles], [], Links, vdash(0,0-A-n,0-B-n)-FProof-FLinks) :-
    focus_shift(Bottom-Proof-OHoles, Links, FLinks),
    residuate(Bottom-Proof,vdash(0,0-A-n,0-B-n)-FProof).

% Keeps resididuating until a sequent of the form
% otimes0(A,B) |- oplus0(C,D) is obtained.    
residuate(vdash(0, 0-otimes0(A,B)-n, 0-oplus0(X,Y)-n)-P, vdash(0, 0-otimes0(A,B)-n, 0-oplus0(X,Y)-n)-P).    
residuate(vdash(0, A, B)-Proof, vdash(0,0-A-n,0-B-n)-FProof) :-
    rule(vdash(0, A, B),vdash(0, A2, B2),Proof, NewProof),
    residuate(vdash(0, A2, B2)-NewProof, vdash(0,0-A-n,0-B-n)-FProof).

% Final step with one closed unfold left, which is unified with the open Goal.
unify_all_open(N, [CBottom-CProof], [], Goal, FLinks, vdash(0,0-A-n,0-B-n)-FProof-FLinks) :- 
    open_goal(Goal),
    unify_open(N, _, CBottom, [Goal], CProof, FLinks, vdash(0,0-A-n,0-B-n)-FProof-[]-[]).

% One open unfold left, that is focus shifted.     
unify_all_open(N, [], [OBottom-OProof-Holes], Goal, Links, vdash(0,0-A-n,0-B-n)-FProof-FLinks) :- 
    open_goal(Goal),
    focus_shift(OBottom-OProof-Holes, Links, FLinks),
    unify_open(N, _, OBottom, [Goal], OProof, FLinks, vdash(0,0-A-n,0-B-n)-FProof-[]-[]).

% An open goal has a non-empty set of holes.    
open_goal(_-_-[_|_]).    
   
% The goal formula can contain holes too, and can be focus shifted.    
unify_all_open(N, [], [Open], GBottom-GProof-[GH|GHoles], Links, FinalBottom-FinalProof-FinalLinks) :- 
    focus_shift(GBottom-GProof-[GH|GHoles], Links, FinalLinks),
    unify_open(N, _, GBottom, [Open], GProof, FinalLinks, FinalBottom-FinalProof-[]-[]).
        
% Closed goal that is unified with an open unfold.    
unify_all_open(N, [], [Open], GBottom-GProof-[], FinalLinks, FinalBottom-FinalProof-FinalLinks) :- 
    unify_open(N, _, GBottom, [Open], GProof, FinalLinks, FinalBottom-FinalProof-[]-[]).
 
% Recursive case: the closed unfold is unified and the updated list of unfolds is passed on. 
unify_all_open(N, [ClosedBottom-ClosedProof|ClosedRest], [O1|AllOpen], Goal, Links, Unified) :- 
    unify_open(N, N1, ClosedBottom, [O1|AllOpen], ClosedProof, Links, NewUnified-NewOpenRest),
    new_closed_open(NewUnified, ClosedRest, NewOpenRest, NewClosed, NewOpen),
    unify_all_open(N1, NewClosed, NewOpen, Goal, Links, Unified).

% If there are no closed unfolds left, an open unfold is chosen using the index N.
%  If this unfold can be focus shifted (ergo it becomes a closed unfold),
%  it is then unified with the other open unfolds.    
unify_all_open(N, [], [O1, O2|AllOpen], Goal, Links, Unified) :- 

    nth0(N, [O1, O2|AllOpen], Bottom-Proof-Holes, OpenRest),
        
    focus_shift(Bottom-Proof-Holes, Links, NewLinks),
        
    unify_open(N, N1, Bottom, OpenRest, Proof, NewLinks, (NewBottom-NewProof-NewHoles)-NewOpenRest),
    
    new_closed_open(NewBottom-NewProof-NewHoles, [], NewOpenRest, NewClosed, NewOpen),
        
    unify_all_open(N1, NewClosed, NewOpen, Goal, NewLinks, Unified).

% Not every open sequent can be focus shifted, and not every open sequent 
% that can be shifted, has to be shifted.      
unify_all_open(N, [], [O1, O2|AllOpen], Goal, Links, Unified) :- 
    N1 is N+1, length([O1, O2|AllOpen], L),N1<L,
    unify_all_open(N1, [], [O1, O2|AllOpen], Goal, Links, Unified).
  
% New unfolds are added to the end of the list of open unfolds 
% if they still contain holes.      
new_closed_open(Bottom-Proof-[], Closed, Open, [Bottom-Proof|Closed], Open).       
new_closed_open(Bottom-Proof-[H|Holes], Closed, Open, Closed, NewOpen) :- 
    append(Open, [Bottom-Proof-[H|Holes]], NewOpen).


% focus_shift(Unfold, OldLinks, NewLinks)
% ===========
%
% Focus shifts all holes of an open unfold, and updates the links.

focus_shift(_-_-[], L, L).        
focus_shift(Bottom-Proof-[vdash(0, _-At/M-_, _-At/N-_)-fr1(idr(At, M, N))-[]|Holes], Links, [M/N|NewLinks]) :-  
    \+var(M),
    atom_pol(At/M,+),
    focus_shift(Bottom-Proof-Holes, Links, NewLinks).
focus_shift(Bottom-Proof-[vdash(0, _-At/M-_, _-At/N-_)-fl1(idl(At, M, N))-[]|Holes], Links, [M/N|NewLinks]) :-
    \+var(N),
    atom_pol(At/M,-),
    focus_shift(Bottom-Proof-Holes, Links, NewLinks).
     
    
%%% unify_open(N, N1, Sequent, Open, SubProof, Constraints, NewUnfold-OpenRest)
%%% ==========================================================
%%%
%%%     N, N1       ==> Indices used for efficient focus shifting
%%%     Sequent     ==> Sequent that is unified to an open unfold
%%%     Open        ==> List of open unfolds
%%%     SubProof    ==> Proof that corresponds to the Sequent that is unified
%%%     Constraints ==> Difference list of constraints
%%%
%%%     NewUnfold-OpenRest 
%%%            <== The unified unfold and the list of open unfolds that are left.

unify_open(N, N1, vdash(F, A, B), Open, SubProof, _Links, VDash-Proof-NewHoles-OpenRest) :- 
    nth0(I, Open, VDash-Proof-ProofHoles, OpenRest),
    select(vdash(F, A, B)-SubProof-Hyps, ProofHoles, NewHoles),
    check_hyps(Hyps, SubProof),
    update_index(I, N, N1).

    
update_index(I, N, N) :- I >= N.
update_index(I, N, N1) :- I < N, N1 is N-1.
 
check_hyps([], _). 
check_hyps([Hyp|Hyps], SubProof) :-
    contains_hyp(SubProof, Hyp),
    check_hyps(Hyps, SubProof).

% contains_term/2 in the occurs library is not sufficient:
%  contains_term(test(1),over(A)) is true, as the variable A is simply unified with the subterm.
%  A hypothesis must be a concrete subterm of its parent argument, so I wrote my own version.   
contains_hyp(P, Hyp) :- 
    \+var(P),
    P =.. [_|Args],
    contains_hyp2(P, Args, Hyp). 
    
contains_hyp2(X, _Args, Hyp) :- Hyp = X.
contains_hyp2(X, Args, Hyp)  :- 
    Hyp \= X,
    contains_hyp3(Args, Hyp).
contains_hyp3([Arg], Hyp) :-  
    contains_hyp(Arg, Hyp).
contains_hyp3([Arg1, Arg2], Hyp) :-
    contains_hyp(Arg1, Hyp) ->
        true
    ;
        contains_hyp(Arg2, Hyp).
 
 
% If unification fails, the actual structural rules of LGs are applied.
% Sequents are 'varred', to prevent undesirable unification.
unify_open(N, N1, vdash(0, A, B),Open, Proof, Links, NewUnfold) :-
    make_var(A, A2),
    make_var(B, B2),
    rule(vdash(0, A2, B2),vdash(0, A3, B3),Proof, NewProof),
    unify_open(N, N1, vdash(0, A3, B3),Open, NewProof, Links, NewUnfold).

make_var(I-X-J, I-var(X)-J) :-    var(X).
make_var(I-X-J, I-X-J)      :- \+ var(X).

unvar(I-var(X)-J,I-X-J).
unvar(I-X-J, I-X-J) :- X \= var(_).
   
% rp1    
% variables are 'unvarred' after each rule    
rule(vdash(0, X2, I-over0(I-Z-K, Y)-_), vdash(0, I-otimes0(X, Y)-K,I-Z-K), F, beta1(F)) :-
    F \= beta(_),
    unvar(X2, X).
rule(vdash(0, Y2, _-under0(X, I-Z-K)-K), vdash(0, I-otimes0(X, Y)-K,I-Z-K), F, gamma1(F)) :-
    F \= gamma(_),
    unvar(Y2, Y).
    
% drp1    
rule(vdash(0, _-obslash0(Y, I-Z-K)-K, X2), vdash(0, I-Z-K, I-oplus0(Y, X)-K), F, gammaplus1(F)) :-
    F \= gammaplus(_),
    unvar(X2, X).
rule(vdash(0, I-oslash0(I-Z-K, X)-_, Y2), vdash(0, I-Z-K, I-oplus0(Y, X)-K), F, betaplus1(F)) :-
    F \= betaplus(_),
    unvar(Y2, Y).
 
% Postulates P1 & P2 (for rightward extraction)
rule(vdash(0, I-otimes0(I-A-J, Y)-K, Z2),vdash(0, I-otimes0(I-otimes0(I-A-J, J-B-K)-K,X-dia0(C)-X)-K,Z),F, xr1(F)) :- 
    \+var(Y),
    Y = J-otimes0(J-B-K, X-dia0(C)-X)-K,
    unvar(Z2, Z).
rule(vdash(0, I-otimes0(Y, J-B-K)-K,Z2),vdash(0, I-otimes0(I-otimes0(A, B)-K,X-dia0(C)-X)-K,Z),F, xr2(F)) :-
    \+var(Y),
    Y = I-otimes0(I-A-J, X-dia0(C)-X)-J,
    unvar(Z2, Z).
        
 % Display postulates for box/diamond.
rule(vdash(0, X2, I-box0(Y)-J),vdash(0, I-dia0(X)-J,Y), F, alpha1(F)) :-
    F \= alpha(_),
    unvar(X2, X).
rule(vdash(0, I-dia0(X)-J, Y2),vdash(0, X, I-box0(Y)-J),F, alpha(F)) :- 
    F \= alpha1(_),
    unvar(Y2, Y).
    
% rp    
rule(vdash(0, I-otimes0(I-X-J, Y)-_, Z2), vdash(0, I-X-J, I-over0(Z, Y)-J), F, beta(F)) :-
    F \= beta1(_),
    unvar(Z2, Z).
rule(vdash(0, _-otimes0(X, J-Y-K)-K, Z2), vdash(0, J-Y-K, J-under0(X, Z)-K), F, gamma(F)) :-
    F \= gamma1(_),
    unvar(Z2, Z).

% drp    
rule(vdash(0, Z2, I-oplus0(I-Y-J, X)-_),vdash(0, I-oslash0(Z, X)-J,I-Y-J), F, betaplus(F)) :-
    F \= betaplus1(_),
    unvar(Z2, Z).
rule(vdash(0, Z2, _-oplus0(Y, J-X-K)-K),vdash(0, J-obslash0(Y, Z)-K,J-X-K),F, gammaplus(F)) :-
    F \= gammaplus1(_),
    unvar(Z2, Z).
    
% g1, g2, g3, g4
rule( vdash(0, I-otimes0(I-X-J, J-Y-K)-K , I-oplus0(I-Z-L, L-W-K)-K), 
      vdash(0, L-obslash0(I-Z-L, I-X-J)-J, L-over0(L-W-K, J-Y-K)-L ), F, gr1(F) ).   
rule( vdash(0, I-otimes0(I-X-J, J-Y-K)-K , I-oplus0(I-Z-L, L-W-K)-K), 
      vdash(0, L-obslash0(I-Z-L, J-Y-K)-K, J-under0(I-X-J, L-W-K)-K), F, gr2(F) ) :-
    I = J;
    I = L.   
rule( vdash(0, I-otimes0(I-X-J, J-Y-K)-K , I-oplus0(I-Z-L, L-W-K)-K), 
      vdash(0, J-oslash0(J-Y-K, L-W-K)-L , J-under0(I-X-J, I-Z-L)-L), F, gr3(F) ).   
rule( vdash(0, I-otimes0(I-X-J, J-Y-K)-K , I-oplus0(I-Z-L, L-W-K)-K), 
      vdash(0, I-oslash0(I-X-J, L-W-K)-L , I-over0(I-Z-L, J-Y-K)-J ), F, gr4(F) ) :-
    J = K;
    L = K.   
