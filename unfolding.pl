/*=====================================================
                        Unfolding
=====================================================*/

:- style_check(-discontiguous).

%%% unfold(InOut, Formula, VDash-Proof-Holes-Hyps, Links)
%%% ============================================================
%%%
%%%     InOut   ==> in, out: determines which side of the sequent is unfolded
%%%     Formula ==> The formula that is unfolded
%%%
%%%     VDash   <== The bottom sequent with labeled atoms
%%%     Proof   <== The proof of the unfolded formula
%%%     Holes   <== List of holes in the proof.
%%%                 Holes are of the form of: VDash-Hole-Hyp, 
%%%                 where Hyp is a list of hypothesis constraints.
%%%     Hyps    <== List of unfolded hypotheses     
%%%     Links   <== A difference list of axiom links

unfold(_, I-J, Atom, I-Atom/M-J, L-L ) :-
    atomic(Atom),!,
    get_label(M).
 
unfold(in, I-J, Formula, vdash(0, LabeledFormula, Structure)-UnfoldedProof-Holes-HypUnfolds, Links) :-
    compound(Formula),
    init_struct(in, I-Formula-J, LabeledFormula, Structure),!,
    g(in, vdash(0, LabeledFormula, Structure),UnfoldedProof, Links, Holes-[], HypUnfolds-[]).
    
unfold(out, I-J, Formula, vdash(0, Structure, LabeledFormula)-UnfoldedProof-Holes-HypUnfolds, Links) :-
    compound(Formula),
    init_struct(out, I-Formula-J, LabeledFormula, Structure),!,
    g(out, vdash(0, Structure, LabeledFormula),UnfoldedProof, Links, Holes-[], HypUnfolds-[]).
           
% Labeling of atoms uses a dynamic predicate at_label/1.
get_label(M) :-
    at_label(M),
    N is M+1,
    retractall(at_label(_)),
    assert(at_label(N)).
 
is_struct(otimes0(_,_)).
is_struct(over0(_,_)).
is_struct(under0(_,_)).
is_struct(oplus0(_,_)).
is_struct(oslash0(_,_)).
is_struct(obslash0(_,_)). 

% init_struct(InOut , Symbol , Formula , LabeledFormula , Structure)
% ===========
%
% Creates an input or output structure.
% The symbol is used later in the computation during the creation of the constraints.

% When a hypothesis is unfolded, its atoms are already labeled    
init_struct(_, I-(I-At/M-J)-J, I-At/M-J, I-_VAR-J).

init_struct(IO, I-(I-Form-J)-J, LabeledForm, Struct) :-
    init_struct(IO, I-Form-J, LabeledForm, Struct).

init_struct(IO, I-Form-J, I-LabeledForm-J, I-Struct-J) :-
    get_bi_struct(IO, IOA-IOB, (I-Form-J)-A-B, LabeledForm-L_A-L_B, Struct-X-Y),
    init_struct(IOA, A, L_A, X),
    init_struct(IOB, B, L_B, Y).

init_struct(IO, I-Form-J, I-LabeledForm-J, I-Struct-J) :-
    get_un_struct(IO, (I-Form-J)-A, LabeledForm-L_A, Struct-X),
    init_struct(IO, A, L_A, X).

% Atom labeling
init_struct(_, I-At-J, I-At/M-J, I-_VAR-J) :-
    atomic(At),
    get_label(M).
          
% Structures matching an in-formula         
get_bi_struct(in, in-in , (_-otimes(A, B)-_)-(_-A-_)-(_-B-_) , otimes(L_A, L_B)-L_A-L_B , _VAR-_-_         ).
get_bi_struct(in, in-out, (I-over(A, B)-J)-(I-A-K)-(J-B-K)  , over(L_A, L_B)-L_A-L_B   , over0(X, Y)-X-Y  ).
get_bi_struct(in, out-in, (J-under(A, B)-K)-(I-A-J)-(I-B-K) , under(L_A, L_B)-L_A-L_B  , under0(X, Y)-X-Y ).

get_bi_struct(in, in-in , (I-oplus(A, B)-K)-(I-A-J)-(J-B-K)   , oplus(L_A, L_B)-L_A-L_B   , oplus0(X, Y)-X-Y ).
get_bi_struct(in, in-out, (_-oslash(A, B)-_)-(_-A-_)-(_-B-_)  , oslash(L_A, L_B)-L_A-L_B  , _VAR-_-_).
get_bi_struct(in, out-in, (_-obslash(A, B)-_)-(_-A-_)-(_-B-_) , obslash(L_A, L_B)-L_A-L_B , _VAR-_-_).

get_un_struct(in, (_-dia(A)-_)-(_-A-_) , dia(L_A)-L_A , _VAR-_    ).
get_un_struct(in, (I-box(A)-J)-(I-A-J) , box(L_A)-L_A , box0(X)-X ).

% Structures matching an out-formula         
get_bi_struct(out, out-out, (I-otimes(A, B)-K)-(I-A-J)-(J-B-K) , otimes(L_A, L_B)-L_A-L_B , otimes0(X, Y)-X-Y ).
get_bi_struct(out, out-in , (_-over(A, B)-_)-(_-A-_)-(_-B-_)   , over(L_A, L_B)-L_A-L_B   , _VAR-_-_).
get_bi_struct(out, in-out , (_-under(A, B)-_)-(_-A-_)-(_-B-_)  , under(L_A, L_B)-L_A-L_B  , _VAR-_-_).

get_bi_struct(out, out-out, (_-oplus(A, B)-_)-(_-A-_)-(_-B-_)   , oplus(L_A, L_B)-L_A-L_B   , _VAR-_-_ ).
get_bi_struct(out, out-in , (I-oslash(A, B)-J)-(I-A-K)-(J-B-K)  , oslash(L_A, L_B)-L_A-L_B  , oslash0(X, Y)-X-Y  ).
get_bi_struct(out, in-out , (J-obslash(A, B)-K)-(I-A-J)-(I-B-K) , obslash(L_A, L_B)-L_A-L_B , obslash0(X, Y)-X-Y ).

get_un_struct(out, (I-dia(A)-J)-(I-A-J) , dia(L_A)-L_A , dia0(X)-X ).
get_un_struct(out, (_-box(A)-_)-(_-A-_) , box(L_A)-L_A , _VAR-_    ).
        

%%% g(InOut, Sequent, Proof, Symbol-Links, Holes, HypUnfolds)
%%% =========================================================
%%%
%%% g is (originally) based on Herman Hendriks (1993) unfolding procedure.
%%% It creates a complete unfold for a given sequent, i.e. a proof, 
%%% a dlist of axiom list, a dlist of open holes and a list of unfolded hypotheses.

    %%% MONOTONICITY RULES %%%
g(InOut, vdash(F, Ant, Suc), Proof, LinksA-LinksC, HolesA-HolesC, HypUnfoldsA-HypUnfoldsC ) :-
    \+var(Ant),\+var(Suc),
    
    g_LGf(InOut, vdash(F, Ant, Suc), InOutA-A, InOutB-B, Proof, ProofA-ProofB ),
        
    g(InOutA, A, ProofA, (LinksA-LinksB), HolesA-HolesB, HypUnfoldsA-HypUnfoldsB ),
    g(InOutB, B, ProofB, (LinksB-LinksC), HolesB-HolesC, HypUnfoldsB-HypUnfoldsC ).

g_LGf(in, vdash(l, I-oplus(A, B)-K, I-oplus0(X, Y)-K) , in-vdash(l, A, X)  , in-vdash(l, B, Y)  , oplus(ProofA, ProofB), ProofA-ProofB).    
g_LGf(in, vdash(l, I-over(B, A)-J , I-over0(Y, X)-J ) , in-vdash(l, B, Y)  , out-vdash(r, X, A) , over(ProofA, ProofB) , ProofA-ProofB).
g_LGf(in, vdash(l, J-under(A, B)-K, J-under0(X, Y)-K) , out-vdash(r, X, A) , in-vdash(l, B, Y)  , under(ProofA, ProofB), ProofA-ProofB).

g_LGf(out, vdash(r, I-otimes0(X, Y)-K , I-otimes(A, B)-K ) , out-vdash(r, X, A) , out-vdash(r, Y, B) , otimes(ProofA, ProofB)  , ProofA-ProofB).
g_LGf(out, vdash(r, I-oslash0(X, Y)-J , I-oslash(A, B)-J ) , out-vdash(r, X, A) , in-vdash(l, B, Y)  , oslash(ProofA, ProofB)  , ProofA-ProofB).
g_LGf(out, vdash(r, J-obslash0(Y, X)-K, J-obslash(B, A)-K) , in-vdash(l, B, Y)  , out-vdash(r, X, A) , obslash(ProofA, ProofB) , ProofA-ProofB).

% box L, dia R    
g(in, vdash(l, I-A-J, I-Y-J), box(Proof),Links, Holes, HypUnfolds) :-
    \+var(A)    , \+var(Y)     ,
    A = box(A2) , Y = box0(Y2) ,
    g(in, vdash(l, A2, Y2),Proof, Links, Holes, HypUnfolds).    

g(out, vdash(r, I-X-J, I-A-J), dia(Proof), Links, Holes, HypUnfolds) :-
    \+var(X)     , \+var(A)    ,
    X = dia0(X2) , A = dia(A2) ,
    g(out, vdash(r, X2, A2),Proof, Links, Holes, HypUnfolds).    

    %%% (DE)FOCUSING %%%  
g(Pol, vdash(0, A, Y), fl1(Proof), Links, Holes, HypUnfolds) :-
    not_var(A), pol(A,-),
    g(Pol, vdash(l, A, Y),Proof, Links, Holes, HypUnfolds).
g(Pol, vdash(r, X, A),fr(Proof), Links, Holes, HypUnfolds) :-
    not_var(A), pol(A,-),
    g(Pol, vdash(0, X, A),Proof, Links, Holes, HypUnfolds).
    
g(Pol, vdash(0, X, A),fr1(Proof),Links, Holes, HypUnfolds) :-
    not_var(A), pol(A,+),
    g(Pol, vdash(r, X, A),Proof, Links, Holes, HypUnfolds).
g(Pol, vdash(l, A, Y),fl(Proof), Links, Holes, HypUnfolds) :-
    not_var(A), pol(A,+),
    g(Pol, vdash(0, A, Y),Proof, Links, Holes, HypUnfolds).
  
  
    %%% (CO)AXIOMS %%%
% Ax - N is unbound
g(in, vdash(l, I-(At/M)-J, I-(At/N)-J), idl(At, M, N), [M/N|L]-L, H-H, Hyps-Hyps) :-
    \+var(M),
    atom_pol(At/M,-).

% CoAx - M is unbound  
g(out, vdash(r, I-(At/M)-J, I-(At/N)-J), idr(At, M, N), [M/N|L]-L, H-H, Hyps-Hyps) :-
    \+var(N),
    atom_pol(At/N,+).
   
   
    %%% OPEN SUBPROOFS / HYPOTHESES %%%
% Negative structure on an out-position (RHS of the sequent)
g(out, vdash(0, X, Y), ProofHole, Links, Hole, HypUnfolds) :- 
    is_var(X),
    pol(Y,-),
    findall_unfolds(out, Y, StructY, Links, HypUnfolds, HypConsts-[]),
    make_hyp_hole(vdash(0, X, StructY), ProofHole, HypConsts, Hole).

% Positive formula on an in-position (LHS of the sequent)
g(in, vdash(0, X, Y), ProofHole, Links, Hole, HypUnfolds) :- 
    is_var(Y),
    pol(X,+),
    findall_unfolds(in, X, StructX, Links, HypUnfolds, HypConsts-[]),
    make_hyp_hole(vdash(0, StructX, Y), ProofHole, HypConsts, Hole).
 
 
% make_hyp_hole(Sequent, ProofHole, Consts, Hole)
% =============
% 
% Adds the hypotheses constraints to the complete hole.

make_hyp_hole(Struct, ProofHole, HypConsts, [Struct-ProofHole-HypConsts|H]-H).
   
   
% findall_unfolds(InOut, Sym, Sequent, Structure, Links, Unfolds, Consts)
% ===============
%
% Finds and unfolds all formulas that are situated on a position (in/out) on which
% they can be unfolded. Also returns an updated list of axiom links and a list of 
% hypotheses constraints that are added to the hole of the initial unfold.   
   
findall_unfolds(in, I-dia(A)-J, I-dia0(X)-J, Links, Unfolds, Consts ) :-
    findall_unfolds(in , A, X, Links, Unfolds, Consts ).
findall_unfolds(out, I-box(A)-J, I-box0(X)-J, Links, Unfolds, Consts ) :-
    findall_unfolds(out, A, X, Links, Unfolds, Consts ).   
findall_unfolds(IO, I-Form-J, I-Struct-J, LinksA-LinksC, UnfoldsA-UnfoldsC, ConstsA-ConstsC ) :-
    \+var(Form),
    get_arg(IO, Form-A-B, Struct-X-Y, IOA, IOB),
    
    findall_unfolds(IOA , A, X, LinksA-LinksB, UnfoldsA-UnfoldsB , ConstsA-ConstsB ),
    findall_unfolds(IOB , B, Y, LinksB-LinksC, UnfoldsB-UnfoldsC , ConstsB-ConstsC ).
       
findall_unfolds(out, I-Form-J, I-Form-J, HypLinks, [Bottom-Proof-Holes-Hyps|U]-U, [Proof|P]-P ) :-
    is_compound(Form),pol(Form,+),
    unfold(out, I-I, Form, Bottom-Proof-Holes-Hyps, HypLinks).

findall_unfolds(in, I-Form-J, I-Form-J, HypLinks, [Bottom-Proof-Holes-Hyps|U]-U, [Proof|P]-P) :-
    is_compound(Form),pol(Form,-),
    unfold(in, I-I, Form, Bottom-Proof-Holes-Hyps, HypLinks).
 
findall_unfolds(_, I-At/M-J, I-At/M-J, L-L, U-U, P-P).

 
get_arg(in, otimes(A, B)-A-B  , otimes0(X, Y)-X-Y  , in  , in  ).
get_arg(in, oslash(A, B)-A-B  , oslash0(X, Y)-X-Y  , in  , out ).    
get_arg(in, obslash(A, B)-A-B , obslash0(X, Y)-X-Y , out , in  ).    

get_arg(out, oplus(A, B)-A-B , oplus0(X, Y)-X-Y , out , out ).
get_arg(out, under(A, B)-A-B , under0(X, Y)-X-Y , in  , out ).
get_arg(out, over(A, B)-A-B  , over0(X, Y)-X-Y  , out , in  ).

% Indexed structure vars.
is_var(_-X-_)  :-   var(X).  
not_var(_-X-_) :- \+var(X).  

% Labeled atoms are compound too (e.g. np/0)
is_compound(Compound) :- 
    compound(Compound),
    Compound \= _/_.