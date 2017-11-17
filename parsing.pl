% A bottom-up parser for the focused Lambek-Grishin Calculus (fLG)
% Bachelor thesis by Jaap Jumelet (2017)
% Under supervision of prof. dr. Michael Moortgat

:- dynamic at_label/1,constraints/1.
:- style_check(-discontiguous).
:- [unification],[unfolding],[latex],[lexicon].


:-  retractall(at_label(_)),
    assert(at_label(0)),
    retractall(constraints(_)),
    assert(constraints(false)).

reset_labels :- 
    retractall(at_label(_)),assert(at_label(0)).

no_constraints :- 
    retractall(constraints(_)),
    assert(constraints(false)).        
constraints :-
    retractall(constraints(_)),
    assert(constraints(true)).
    
/*=====================================================
                    Bottom-up Parsing
=====================================================*/
    
% example input:
% ?- sen(S), parse(0,S,s). "everyone thinks some teacher likes bob"
% ?- parse(0,dia(box(dia(box(a)))),dia(box(a))). <- 2 derivations
    
%%% parse(Focus, In, Out)
%%% =====================
%%%
%%%     Focus  ==> l,0, r (left, neutral, right)
%%%     In, Out ==> 2 lists of lexical items or formulas, or a single structure/formula
%%%

parse(F, In, Out) :-
    reset_labels,
    
    % Create all unfolded formulas    
    get_in_out(In, Out, In2, Out2, Sentence, IO-Goal), 
    get_unfolds(in, 0, In2, InUnfolds, InLinks-[]),

    (IO = in ->
        make_goal(IO-Goal, GoalUnfold, OpenHypGoals, ClosedHypGoals, GoalLinks-InLinks),
        get_unfolds(out, 0, Out2, OutUnfolds, Links-GoalLinks)
    ;
        get_unfolds(out, 0, Out2, OutUnfolds, OutLinks-InLinks),
        make_goal(IO-Goal, GoalUnfold, OpenHypGoals, ClosedHypGoals, Links-OutLinks)),

    get_labeled_forms(in  , InUnfolds  , InLabeledForms  ),
    get_labeled_forms(out , OutUnfolds , OutLabeledForms ),
    get_labeled_form(IO, GoalUnfold-_, LabeledGoal),
        
    conc(InUnfolds,OutUnfolds,AllUnfolds-[]),    
    open_closed(AllUnfolds, OpenUnfolds-OpenHypGoals, ClosedUnfolds-ClosedHypGoals),
    
    !, % Unfolding phase is deterministic
    time(
    % Unify all open gaps by linking them 
    findall(term(FinalProof,FinalLinks,UnifiedIn,UnifiedOut,SentenceTree),
    ((
    unify_all_open(0, ClosedUnfolds,
                     OpenUnfolds,
                     GoalUnfold,
                     Links,
                     vdash(0, FinalIn, FinalOut)-CompleteProof-FinalLinks),
    
    % Fill in the gaps that are left by atomic formulas, word order is preserved
    unify_in(FinalIn, InLabeledForms, LabeledGoal, Sentence, UnifiedIn, SentenceTree, []-[]),
    unify_out(FinalOut, OutLabeledForms, LabeledGoal, UnifiedOut, []),
    add_init_focus(F, FinalIn, FinalOut, CompleteProof, FinalProof))),[P|Proofs])),!,

    print_latex([P|Proofs]),tex_display.

    
    
   
% get_in_out(InitIn, InitOut, In, Out, Sentence, IOGoal-Goal)
% ==========
%
% For efficiency reasons, the final goal is separated from the other unfolds.   
% IOGoal is used for the unfolding of the goal formula.

get_in_out([In], Out , In2 , Out2 , Sen , Goal    ) :- 
    !,get_in_out(In, Out, In2, Out2, Sen, Goal).
get_in_out(In ,[Out], In2 , Out2 , Sen , Goal    ) :- 
    !,get_in_out(In, Out, In2, Out2, Sen, Goal).
get_in_out(In , Out , In2 , Out2 , In  , _-[]    ) :- is_list(In), is_list(Out),!, 
    get_forms(In, In2), 
    get_forms(Out, Out2).
get_in_out(In , Out , In2 , []   , In  , out-Out ) :- is_list(In) , \+is_list(Out),!, 
    get_forms(In, In2).
get_in_out(In , Out , []  , Out2 , [In], in-In   ) :- is_list(Out),!, 
    get_forms(Out, Out2).
get_in_out(In , Out , []  ,[Out2], [In], in-In2  ) :- 
    get_form(In, In2)  , 
    (pol(In2,+) ;atomic(In2),atom_pol(In2/_ ,+)), 
    get_form(Out, Out2).
get_in_out(In , Out , [In2], []  , [In], out-Out2) :- get_form(Out, Out2), (pol(Out2,-);atomic(Out2),atom_pol(Out2/_,-)), get_form(In, In2).

 
% get_unfolds(InOut, Focus, Input, Unfolds, AxiomLinks)
% ===========
% 
% unfolds a list of formulas, and returns a difference list of unfolds and axiom links.

get_unfolds(_, _, [], U-U, L-L).
get_unfolds(IO, I, [Form], [Unfold|U]-U, Links) :-
    unfold(IO, I-n, Form, Unfold, Links).
get_unfolds(IO, I, [Form|Forms], [Unfold|Unfolds]-U, LinksA-LinksC ) :-
    J is I+1,
    unfold(IO, I-J, Form, Unfold, LinksA-LinksB),
    get_unfolds(IO, J, Forms, Unfolds-U, LinksB-LinksC).
 

% get_forms(Input, Formula)
% =========
% 
% Returns a formula if the input is in the lexicon, otherwise it returns the input itself.
 
get_forms(In, Forms) :-
    maplist(get_form, In, Forms).
get_form(Word, Formula) :-
    lex(Word, Formula).
get_form(Formula, Formula) :-
    \+lex(Formula, _).

    
% get_labeled_forms(IO, Unfolds, LabeledForms)
% =================
% 
% Returns a list of labeled formulas, given a list of unfolded formulas.
     
get_labeled_forms(IO, [F|Fs]-_, [L|Ls]) :-
    \+var(F),
    get_labeled_form(IO, F, L),
    get_labeled_forms(IO, Fs-_, Ls).
get_labeled_forms(_, U-U, []).
 
 
get_labeled_form(in, vdash(_, F, _)-_-_-_, F).    
get_labeled_form(out, vdash(_, _, F)-_-_-_, F).    
get_labeled_form(_, []-_ , [] ).
get_labeled_form(_, I-(F/M)-J, I-(F/M)-J).   
    
    
% open_closed(Unfolds, OpenUnfolds, ClosedUnfolds)
% ===========
%
% Returns 2 difference lists of open & closed unfolds.    
% Closed formulas have an empty set of holes and no hypotheses.
% Atomic formulas are discarded at this point.

open_closed([], O-O, C-C).
open_closed([A-B-[]-[]|Unfolds], Open, [A-B|ClosedRest]-C) :-  
    open_closed(Unfolds, Open, ClosedRest-C).

open_closed([_-(_A/_M)-_|Unfolds], Open, Closed) :-
    open_closed(Unfolds, Open, Closed).
    
open_closed([U-Hyps|Unfolds], [U|Open]-O, Closed-C) :- 
    open_closed(Hyps, OpenHyps-O, ClosedHyps-C),
    open_closed(Unfolds, Open-OpenHyps, Closed-ClosedHyps).   
  
  
% make_goal(IO-Goal, GoalUnfold, GoalOpen, GoalClosed, GoalLinks)
% =========
%
% Creates the unfold of the goal formula. 
% Unfolding depends on whether the goal is compound or atomic.
 
make_goal(_-[], [], [], [], L-L).
make_goal(IO-Goal, GoalUnfold, GoalOpen, GoalClosed, GoalLinks) :-
    compound(Goal),
    make_compound_goal(IO, Goal, GoalUnfold, GoalOpen, GoalClosed, GoalLinks).
make_goal(IO-Goal, GoalUnfold, [], [], L-L) :-
    atomic(Goal),
    make_atomic_goal(IO, Goal, GoalUnfold).
    
make_compound_goal(IO, Goal, GoalUnfold, OpenGoals, ClosedGoals, GoalLinks) :-   
    unfold(IO, 0-n, Goal, GoalUnfold-Hyps, GoalLinks),
    open_closed(Hyps, OpenGoals-[], ClosedGoals-[]).
 
make_atomic_goal(out, Goal, vdash(0, 0-X-n, 0-Goal/M-n)-H-[vdash(0, 0-X-n, 0-Goal/M-n)-H-[]] ) :- 
    get_label(M).
make_atomic_goal(in,  Goal, vdash(0, 0-Goal/M-n, 0-Y-n)-H-[vdash(0, 0-Goal/M-n, 0-Y-n)-H-[]] ) :- 
    get_label(M).
  
  
% add_init_focus(Foc, In, Out, Proof, FinalProof)
% ==============
%  
% Adds the initial focus of the sequent at the bottom of the proof. 
% An initial focus for a proof that is brought into that focus already,
% means we can remove that step in the derivation.

add_init_focus(0, _In, _Out, Proof, Proof).
add_init_focus(l, _, _, fl1(Proof),Proof).
add_init_focus(r, _, _, fr1(Proof),Proof).        

add_init_focus(l, In, _Out, Proof, fl(Proof)) :- pol(In,+).
add_init_focus(r, _In, Out, Proof, fr(Proof)) :- pol(Out,-).        
        
        
% unify_in(InStruct, InForms, Goal, SenList, FinalInStruct, SenStruct, Rest)
% ========
%
% unify_in/7 unifies the atomic formulas of the input (InForms) with the  
% structure that is derived during the parsing process. It also builds up 
% the sentence structure: e.g. alice*(likes*bob).

% If the input formula is the final goal, it is separated from the input list at
% the beginning of the parsing process.
unify_in(I-Goal-J, [], I-Goal-J, [W], Goal2, W, []-[]) :-
    remove_indices(Goal,Goal2).

unify_in(I-In-J, [I-In-J|InRest], _, [W|SenRest], In2, W, InRest-SenRest) :-
    remove_indices(In,In2).
unify_in(_-otimes0(X, Y)-_,I, _, S, otimes0(IX, IY), SX*SY, InRest2-SenRest2) :- 
    unify_in(X, I, _, S, IX, SX, InRest-SenRest),
    unify_in(Y, InRest, _, SenRest, IY, SY, InRest2-SenRest2).
    
% unify_out(OutStruct, OutForms, Goal, FinalOutStruct, Rest)
% =========
%
% Similar to unify_in/7, but for out-structures (on the rhs).
    
unify_out(I-Goal-J, [], I-Goal-J, Goal2, []) :-
    remove_indices(Goal,Goal2).    
unify_out(I-Out-J, [I-Out-J|OutRest], _, Out2, OutRest) :-
    remove_indices(Out,Out2).
unify_out(_-oplus0(X, Y)-_,O, _, oplus0(OX, OY), OutRest2) :-
    unify_out(X, O, _, OX, OutRest),
    unify_out(Y, OutRest, _, OY, OutRest2).
 
 
remove_indices(At/N, At/N). 
remove_indices(_-F-_, F2) :-
    remove_indices(F,F2). 
 
% This could be simplified by =.., but that is heavier on computation. 
remove_indices(otimes(A,B), otimes(A2,B2)) :-
    remove_indices(A, A2),
    remove_indices(B, B2).
remove_indices(over(A,B), over(A2,B2)) :-
    remove_indices(A, A2),
    remove_indices(B, B2).
remove_indices(under(A,B), under(A2,B2)) :-
    remove_indices(A, A2),
    remove_indices(B, B2).
 
remove_indices(oplus(A,B), oplus(A2,B2)) :-
    remove_indices(A, A2),
    remove_indices(B, B2).
remove_indices(oslash(A,B), oslash(A2,B2)) :-
    remove_indices(A, A2),
    remove_indices(B, B2).
remove_indices(obslash(A,B), obslash(A2,B2)) :-
    remove_indices(A, A2),
    remove_indices(B, B2). 
    
remove_indices(box(A), box(A2)) :-
    remove_indices(A, A2).
remove_indices(dia(A), dia(A2)) :-
    remove_indices(A, A2).
 
 
% aux preds
 
lift(F, under(over(s, F),s)). 
form(1, under(over(s, under(np, s)),s)).
form(2, over(under(np, s),np)).
form(3, over(under(n, n),over(s, dia(box(np))))).
sen([everyone, thinks, some, teacher, likes, bob]).

conc(A-B,B-C,A-C).

printlist([]).    
printlist([H|T]) :-
        print(H),nl, nl, printlist(T).
 
% polarity: negative: mono left ; positive: mono right

% Polarity for indexed formulas
pol(_-X-_,P) :- pol(X,P).

pol(box(_),-).
pol(oplus(_, _),-).
pol(over(_, _),-).
pol(under(_, _),-).

pol(dia(_),+).
pol(otimes(_, _),+).
pol(oslash(_, _),+).
pol(obslash(_, _),+).

pol(A/_, Pol) :- atom_pol(A/_, Pol).

% atom_pol/2: choose bias for atoms (adapt to your own liking)

atom_pol(A/_, Pol) :- A=s -> Pol=(-) ; Pol=(+).

% Prints the latex output of unfolding In.
% Note: does not work for a hole with more than one hypothesis.
latex_unfold(IO,In) :- 
  %  reset_labels,
    (lex(In,Form);Form = In),!,
    unfold(IO, 3-4, Form, U, _),
    print_unfold(U),
    tex_display,!.
    