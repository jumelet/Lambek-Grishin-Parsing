/*=====================================================
                      LaTeX output
=====================================================*/
%%%
%%% This code is an edited version of the latex output by prof. dr. Michael Moortgat.
%%% Semantic terms are removed, but they are easy to add.
%%%

:- style_check(-discontiguous).
:- dynamic hyp_holes/1.

show(index).

% put your system dependent shell commands here
% for typesetting display.tex, and viewing the result

tex_display:-
	shell('pdflatex lgfout > /dev/null'),
	shell('cmd.exe /C start lgfout.pdf').

print_unfold(Unfold) :-
        numbervars(Unfold),
        tell('lgfout.tex'),
		writeln('\\documentclass[]{article}'),
		writeln('\\usepackage[pdftex,active,tightpage]{preview}'),
		writeln('\\usepackage{calc}'),
		writeln('\\usepackage{graphicx}'),
		writeln('\\usepackage{amssymb}'),
		writeln('\\usepackage{amsmath}'),
		writeln('\\usepackage{stmaryrd}'),
		writeln('\\usepackage{proof}'),
        writeln('\\usepackage{mathtools}'),
        writeln('\\newcommand{\\indexed}[3]{~{}^{#1}#2^{#3}~}'),
        writeln('\\newcommand{\\bigindexed}[3]{\\prescript{#1}{}{\\big(}#2\\big)^{#3}}'),
		writeln('\\newcommand{\\fboxx}[1]{\\fbox{$#1$}}'),
		writeln('\\newcommand{\\bs}{\\backslash}'),
		writeln('\\pagestyle{empty}'),
		writeln('\\begin{document}'),
		writeln('\\addtolength{\\inferLineSkip}{2pt}'),
		writeln('\\setlength{\\PreviewBorder}{.5in}'),!,
        print_unfold1(Unfold),
        writeln('\\end{document}'),
        told.
    
print_latex(Proofs) :-
        tell('lgfout.tex'),
		writeln('\\documentclass[]{article}'),
		writeln('\\usepackage[pdftex,active,tightpage]{preview}'),
		writeln('\\usepackage{calc}'),
		writeln('\\usepackage{graphicx}'),
		writeln('\\usepackage{amssymb}'),
		writeln('\\usepackage{amsmath}'),
		writeln('\\usepackage{stmaryrd}'),
		writeln('\\usepackage{proof}'),
		writeln('\\newcommand{\\fboxx}[1]{\\fbox{$#1$}}'),
		writeln('\\newcommand{\\bs}{\\backslash}'),
		writeln('\\pagestyle{empty}'),
		writeln('\\begin{document}'),
		writeln('\\addtolength{\\inferLineSkip}{2pt}'),
		writeln('\\setlength{\\PreviewBorder}{.5in}'),!,
        print_list1(Proofs),
        writeln('\\end{document}'),
        told.

% print_list1/4: the actual shipping out of tex proofs/terms
% the show/1 flags determine what is shown (values: proof, ch, sem, lex, index)
% default: show(proof), show(ch)
	
print_list1([]).

% sequents

print_list1([term(Combinator,Axioms,A,S,St)|Xs]) :- 
		once(arrow2seq(Combinator,A,S,Proof)),
        telling(Stream),
        tell(user),
		writeln(Combinator),nl, % combinator is sent to interpreter window
        writeln(Axioms),nl,     % so is the axiom linking
        writeln(St),nl,         % and the sentence tree
        tell(Stream),
        writeln('\\begin{preview}'),
        writeln('$\\begin{array}{c}'),
        write_proof(Proof),
  		nl, 
        writeln('\\end{array}$'),              
        writeln('\\end{preview}'),
        !,
        print_list1(Xs).
 
print_unfold1(vdash(0, LabeledFormula, Structure)-UnfoldedProof-Holes-HypUnfolds) :- 
        retractall(hyp_holes(_)),
        assert(hyp_holes(Holes-HypUnfolds)),
    	once(arrow2seq(UnfoldedProof,LabeledFormula,Structure,Proof)),
        telling(Stream),
        tell(user),
		writeln(UnfoldedProof),nl, 
		writeln(Holes),nl, 
		writeln(HypUnfolds),nl, 
        tell(Stream),
        writeln('\\begin{preview}'),
        writeln('$\\begin{array}{c}'),!,
        write_proof(Proof),
  		nl, 
        writeln('\\end{array}$'),              
        writeln('\\end{preview}'),
        !.
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%               
% IV. From arrows to sequents: Curry-Howard + MILL interpretation 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

% The translation from categorical (Combinator) to sequent derivation (Proof)
% involves expansion with the rewrite rules, replacing a logical nnective
% by its structural proxy (left rules for otimes, oslash, obslash; right rules
% for oplus, over, under).

arrow2seq(P,_-A-_,_-B-_,P2) :- 
    arrow2seq(P,A,B,P2).

arrow2seq('$VAR'(N),_,_,hole('$VAR'(N))).

arrow2seq(idr(A,N,M),A/N,A/M,rule0(ax,A/N,A/M)).
arrow2seq(idl(A,N,M),A/N,A/M,rule0(coax,A/N,A/M)).

% (de)focusing 

arrow2seq(fl(F),A,B,rule1(fl,A,B,Tree)) :-
        arrow2seq(F,A,B,Tree).
arrow2seq(fr(F),A,B,rule1(fr,A,B,Tree)) :-
        arrow2seq(F,A,B,Tree).
                        
arrow2seq(fl1(F),A,B,rule1(fl1,A,B,Tree)) :-
        arrow2seq(F,A,B,Tree).
arrow2seq(fr1(F),A,B,rule1(fr1,A,B,Tree)) :-
        arrow2seq(F,A,B,Tree).

% monotonicity rules
          
arrow2seq(dia(F),dia0(A),dia(B),rule1(dia(right),dia0(A),dia(B),Tree)) :-
		arrow2seq(F,A,B,Tree).
arrow2seq(box(F),box(A),box0(B),rule1(box(left),box(A),box0(B),Tree)) :-
		arrow2seq(F,A,B,Tree).
		
arrow2seq(otimes(F,G),otimes0(A,B),otimes(C,D),
			rule2(otimes(right),otimes0(A,B),otimes(C,D),Tree1,Tree2)) :-
        arrow2seq(F,A,C,Tree1),
        arrow2seq(G,B,D,Tree2).
arrow2seq(over(F,G),over(A,B),over0(C,D),
			rule2(over(left),over(A,B),over0(C,D),Tree1,Tree2)) :-
        arrow2seq(F,A,C,Tree1),
        arrow2seq(G,D,B,Tree2).
arrow2seq(under(F,G),under(A,B),under0(C,D),
			rule2(under(left),under(A,B),under0(C,D),Tree1,Tree2)) :-
        arrow2seq(F,C,A,Tree1),
        arrow2seq(G,B,D,Tree2).
        
arrow2seq(oplus(F,G),oplus(A,B),oplus0(C,D),
			rule2(oplus(left),oplus(A,B),oplus0(C,D),Tree1,Tree2)) :-
        arrow2seq(F,A,C,Tree1),
        arrow2seq(G,B,D,Tree2).
arrow2seq(oslash(F,G),oslash0(A,B),oslash(C,D),
			rule2(oslash(right),oslash0(A,B),oslash(C,D),Tree1,Tree2)) :-
        arrow2seq(F,A,C,Tree1),
        arrow2seq(G,D,B,Tree2).
arrow2seq(obslash(F,G),obslash0(A,B),obslash(C,D),
			rule2(obslash(right),obslash0(A,B),obslash(C,D),Tree1,Tree2)) :-
        arrow2seq(F,C,A,Tree1),
        arrow2seq(G,B,D,Tree2).

% neutral: insert rewrite rules (rewrite/9, expand/8)

arrow2seq(Combinator,In,Out,ProofOut) :-
	neutral(Combinator), % (dual) residuation rules, distributivity rules
	rewrite(In,Out,Ins,Outs,s(K),0),
	expand(s(K),In,Out,[In-Out],Proof0,ProofOut),
	!,
	arrow2seq(Combinator,Ins,Outs,Proof0).

neutral(Cmb) :- \+var(Cmb),
	Cmb=..[Op,_],
	member(Op,[fl1,fr1, % left/rightharpoonup
				alpha,alpha1, % unary rp
				beta,beta1,gamma,gamma1, % rp
				betaplus,betaplus1,gammaplus,gammaplus1, % drp
				g1,g2,g3,g4, % distributivity
				xr1,xl1,xr2,xl2] % extraction
				).    
    
% display rules

arrow2seq(alpha(F),A,box0(B),
			rule1(alpha,A,box0(B),Tree)) :-
		arrow2seq(F,dia0(A),B,Tree).
arrow2seq(alpha1(F),dia0(A),B,
			rule1(alpha1,dia0(A),B,Tree)) :-
		arrow2seq(F,A,box0(B),Tree).
				
arrow2seq(beta(F),A,over0(C,B),
			rule1(rp,A,over0(C,B),Tree)) :-
        arrow2seq(F,otimes0(A,B),C,Tree).
arrow2seq(beta1(F),otimes0(A,B),C,
			rule1(rp,otimes0(A,B),C,Tree)) :-
        arrow2seq(F,A,over0(C,B),Tree).
arrow2seq(gamma(F),B,under0(A,C),
			rule1(rp,B,under0(A,C),Tree)) :-
        arrow2seq(F,otimes0(A,B),C,Tree).
arrow2seq(gamma1(F),otimes0(A,B),C,
			rule1(rp,otimes0(A,B),C,Tree)) :-
        arrow2seq(F,B,under0(A,C),Tree).
                
arrow2seq(betaplus(F),oslash0(C,B),A,
			rule1(drp,oslash0(C,B),A,Tree)) :-
        arrow2seq(F,C,oplus0(A,B),Tree).
arrow2seq(betaplus1(F),C,oplus0(A,B),
			rule1(drp,C,oplus0(A,B),Tree)) :-
        arrow2seq(F,oslash0(C,B),A,Tree).
arrow2seq(gammaplus(F),obslash0(A,C),B,
			rule1(drp,obslash0(A,C),B,Tree)) :-
        arrow2seq(F,C,oplus0(A,B),Tree).
arrow2seq(gammaplus1(F),C,oplus0(A,B),
			rule1(drp,C,oplus0(A,B),Tree)) :-
        arrow2seq(F,obslash0(A,C),B,Tree).

% extraction

arrow2seq(xr1(F),otimes0(otimes0(A,B),dia0(C)),D,
			rule1(xr1,otimes0(otimes0(A,B),dia0(C)),D,Tree)) :-
		arrow2seq(F,otimes0(A,otimes0(B,dia0(C))),D,Tree).
arrow2seq(xr2(F),otimes0(otimes0(A,B),dia0(C)),D,
			rule1(xr2,otimes0(otimes0(A,B),dia0(C)),D,Tree)) :-
		arrow2seq(F,otimes0(otimes0(A,dia0(C)),B),D,Tree). 
		
arrow2seq(xl1(F),otimes0(A,B),under0(dia0(C),D),
			rule1(xl1,otimes0(A,B),under0(dia0(C),D),Tree)) :-
		arrow2seq(F,otimes0(dia0(C),A),over0(D,B),Tree).
arrow2seq(xl2(F),otimes0(A,B),under0(dia0(C),D),
			rule1(xl2,otimes0(A,B),under0(dia0(C),D),Tree)) :-
		arrow2seq(F,otimes0(dia0(C),B),under0(A,D),Tree).

% distributivity rules

arrow2seq(g1(F),obslash0(A,B),over0(D,C),
			rule1(g1,obslash0(A,B),over0(D,C),Tree)) :-
        arrow2seq(F,otimes0(B,C),oplus0(A,D),Tree).
arrow2seq(g2(F),obslash0(B,C),under0(A,D),
			rule1(g2,obslash0(B,C),under0(A,D),Tree)) :-
        arrow2seq(F,otimes0(A,C),oplus0(B,D),Tree).
arrow2seq(g3(F),oslash0(B,C),under0(A,D),
			rule1(g3,oslash0(B,C),under0(A,D),Tree)) :-
        arrow2seq(F,otimes0(A,B),oplus0(D,C),Tree).
arrow2seq(g4(F),oslash0(A,B),over0(D,C),
			rule1(g4,oslash0(A,B),over0(D,C),Tree)) :-
        arrow2seq(F,otimes0(A,C),oplus0(D,B),Tree).

%%%%%% rewrite/10, expand/8 %%%%%%

% rewrite/10: 
%	rewrite(A,B,CommandIn_,CommandIn,StructuralA,StructuralB,CommandOut_,CommandOut,Succ,Diff)

rewrite(A,B,As,Bs,K,M) :-
	in(A,As,K,L),
	out(B,Bs,L,M).

in(dia0(A),dia0(As),K,L) :-
	!,
	in(A,As,K,L).

in(otimes0(A,B),otimes0(As,Bs),K,M) :-
	!,
	in(A,As,K,L),
	in(B,Bs,L,M).
in(oslash0(A,B),oslash0(As,Bs),K,M) :-
	!,
	in(A,As,K,L),
	out(B,Bs,L,M).
in(obslash0(A,B),obslash0(As,Bs),K,M) :-
	!,
	out(A,As,K,L),
	in(B,Bs,L,M).

in(dia(A),dia0(As),s(K),L) :-
	!,
	in(A,As,K,L).
	
in(otimes(A,B),otimes0(As,Bs),s(K),M) :-
	!,
	in(A,As,K,L),
	in(B,Bs,L,M).
in(oslash(A,B),oslash0(As,Bs),s(K),M) :-
	!,
	in(A,As,K,L),
	out(B,Bs,L,M).
in(obslash(A,B),obslash0(As,Bs),s(K),M) :-
	!,
	out(A,As,K,L),
	in(B,Bs,L,M).
	
in(A,A,K,K).

out(box0(A),box0(As),K,L) :-
	!,
	out(A,As,K,L).
	
out(oplus0(A,B),oplus0(As,Bs),K,M) :-
	!,
	out(A,As,K,L),
	out(B,Bs,L,M).
out(over0(A,B),over0(As,Bs),K,M) :-
	!,
	out(A,As,K,L),
	in(B,Bs,L,M).
out(under0(A,B),under0(As,Bs),K,M) :-
	!,
	in(A,As,K,L),
	out(B,Bs,L,M).

out(box(A),box0(As),s(K),L) :-
	!,
	out(A,As,K,L).
	
out(oplus(A,B),oplus0(As,Bs),s(K),M) :-
	!,
	out(A,As,K,L),
	out(B,Bs,L,M).
out(over(A,B),over0(As,Bs),s(K),M) :-
	!,
	out(A,As,K,L),
	in(B,Bs,L,M).
out(under(A,B),under0(As,Bs),s(K),M) :-
	!,
	in(A,As,K,L),
	out(B,Bs,L,M).
	
out(A,A,K,K).

% expand/8: expand(Depth,In,Out,Closed,ProofIn,ProofOut)

expand(0,_,_,_,Proof,Proof).

expand(s(K),dia(A),Out,_,Proof0,
			rule1(dia(left),dia(A),Out,Proof)) :-
		expand(K,dia0(A),Out,[dia0(A)-Out],
			Proof0,Proof).
			
expand(s(K),otimes(A,B),Out,_,Proof0,
			rule1(otimes(left),otimes(A,B),Out,Proof)) :-
		expand(K,otimes0(A,B),Out,[otimes0(A,B)-Out],
			Proof0,Proof).
		
expand(s(K),oslash(A,B),Out,_,Proof0,
			rule1(oslash(left),oslash(A,B),Out,Proof)) :-
		expand(K,oslash0(A,B),Out,[oslash0(A,B)-Out],
			Proof0,Proof).
		
expand(s(K),obslash(A,B),Out,_,Proof0,
			rule1(obslash(left),obslash(A,B),Out,Proof)) :-
		expand(K,obslash0(A,B),Out,[obslash0(A,B)-Out],
			Proof0,Proof).

expand(s(K),In,box(A),_,Proof0,
			rule1(box(right),In,box(A),Proof)) :-
		expand(K,In,box0(A),[In-box0(A)],
			Proof0,Proof).
															
expand(s(K),In,oplus(A,B),_,Proof0,
			rule1(oplus(right),In,oplus(A,B),Proof)) :-
		expand(K,In,oplus0(A,B),[In-oplus0(A,B)],
			Proof0,Proof).
		
expand(s(K),In,over(A,B),_,Proof0,
			rule1(over(right),In,over(A,B),Proof)) :-
		expand(K,In,over0(A,B),[In-over0(A,B)],
			Proof0,Proof).
		
expand(s(K),In,under(A,B),_,Proof0,
			rule1(under(right),In,under(A,B),Proof)) :-
		expand(K,In,under0(A,B),[In-under0(A,B)],
			Proof0,Proof).

% if the above fail, apply rd/drp rules to display the formula to be rewritten 

expand(s(K),dia0(A),B,Closed0,Proof0,rule1(rp,dia0(A),B,Proof)) :-
		insert(Closed0,A-box0(B),Closed),
		expand(s(K),A,box0(B),Closed,Proof0,Proof).
expand(s(K),A,box0(B),Closed0,Proof0,rule1(rp,A,box0(B),Proof)) :-
		insert(Closed0,dia0(A)-B,Closed),
		expand(s(K),dia0(A),B,Closed,Proof0,Proof).
				
expand(s(K),otimes0(A,B),C,Closed0,Proof0,rule1(rp,otimes0(A,B),C,Proof)) :-
		insert(Closed0,A-over0(C,B),Closed),
		expand(s(K),A,over0(C,B),Closed,Proof0,Proof).

expand(s(K),otimes0(A,B),C,Closed0,Proof0,rule1(rp,otimes0(A,B),C,Proof)) :-
		insert(Closed0,B-under0(A,C),Closed),
		expand(s(K),B,under0(A,C),Closed,Proof0,Proof).

expand(s(K),oslash0(A,B),C,Closed0,Proof0,rule1(drp,oslash0(A,B),C,Proof)) :-
		insert(Closed0,A-oplus0(C,B),Closed),
		expand(s(K),A,oplus0(C,B),Closed,Proof0,Proof).

expand(s(K),obslash0(A,B),C,Closed0,Proof0,rule1(drp,obslash0(A,B),C,Proof)) :-
		insert(Closed0,B-oplus0(A,C),Closed),
		expand(s(K),B,oplus0(A,C),Closed,Proof0,Proof).

expand(s(K),A,oplus0(B,C),Closed0,Proof0,rule1(drp,A,oplus0(B,C),Proof)) :-
		insert(Closed0,obslash0(B,A)-C,Closed),
		expand(s(K),obslash0(B,A),C,Closed,Proof0,Proof).

expand(s(K),A,oplus0(B,C),Closed0,Proof0,rule1(drp,A,oplus0(B,C),Proof)) :-
		insert(Closed0,oslash0(A,C)-B,Closed),
		expand(s(K),oslash0(A,C),B,Closed,Proof0,Proof).

expand(s(K),A,over0(B,C),Closed0,Proof0,rule1(rp,A,over0(B,C),Proof)) :-
		insert(Closed0,otimes0(A,C)-B,Closed),
		expand(s(K),otimes0(A,C),B,Closed,Proof0,Proof).

expand(s(K),A,under0(B,C),Closed0,Proof0,rule1(rp,A,under0(B,C),Proof)) :-
		insert(Closed0,otimes0(B,A)-C,Closed),
		expand(s(K),otimes0(B,A),C,Closed,Proof0,Proof).



% insert/3: insert(ListIn,Element,ListOut) adds Element to
%	ListIn if it isn't there already

insert([],A,[A]).
insert([X|Xs],A,[X|Ys]) :-
        X \== A,
        insert(Xs,A,Ys).

 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% From here on: boring typesetting routines
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
        
write_proof(hole(Var)) :- hyp_holes(Holes-_),
        member((vdash(0,A,S)-Var-HypConsts),Holes),
        write(' \\infer*{'),
        write_formula(0,A),
        write(' \\vdash '),
        write_formula(0,S),
        write(' }{'),
        write_hyps(HypConsts),
        write('}').

write_hyps([]).
write_hyps([P,P2|Hyps]) :-
        hyp_holes(Holes-Hyps),
        member(vdash(0,A,S)-P-HolesH-HypsH,Hyps),
        append(Holes,HolesH,HolesN),
        append(Hyps,HypsH,HypsN),
        retractall(hyp_holes(_)),
        assert(hyp_holes(HolesN-HypsN)),
    	once(arrow2seq(P,A,S,Proof)),
        write_proof(Proof),
        write(' & '),
        write_hyps([P2|Hyps]).
write_hyps([P]) :-
        hyp_holes(Holes-Hyps),
        member(vdash(0,A,S)-P-HolesH-HypsH,Hyps),
        append(Holes,HolesH,HolesN),
        append(Hyps,HypsH,HypsN),
        retractall(hyp_holes(_)),
        assert(hyp_holes(HolesN-HypsN)),
    	once(arrow2seq(P,A,S,Proof)),
        write_proof(Proof).        
        
get_var('$VAR'(N),Char) :- Code is N+65,char_code(Char,Code).
        
write_proof(rule0(coax,A/N,A/M)) :-
		write(' \\infer{\\fboxx{'),
        write_formula(0,A/N),
        write('} \\vdash '),
        write_formula(0,A/M),
        write('}{'),
        %write_sem(Alpha,1),
        write('}').
write_proof(rule0(ax,A/N,A/M)) :-
		write(' \\infer{'),
        write_formula(0,A/N),
        write(' \\vdash \\fboxx{'),
        write_formula(0,A/M),
        write('}}{'),
        %write_sem(Var,1),
        write('}').


% unary focused        
write_proof(rule1(R,A,B,Proof)) :-
        member(R,[fl,box(left)]),
        write(' \\infer['),
        write_rule(R),
        write(']{\\fboxx{'),
        write_formula(0,A),
        write('} \\vdash '),
        write_formula(0,B),
        write('}{'),
        write_proof(Proof),
        write('}').
write_proof(rule1(R,A,B,Proof)) :-
        member(R,[fr,dia(right)]),
        write(' \\infer['),
        write_rule(R),
        write(']{'),
        write_formula(0,A),
        write(' \\vdash \\fboxx{'),
        write_formula(0,B),
        write('}}{'),
        write_proof(Proof),
        write('}').
 
write_proof(rule1(R,A,B,Proof)) :-
        member(R,[alpha,alpha1]),
        write(' \\infer['),
        write_rule(R),
        write(']{'),
        write_formula(0,A),
        write(' \\vdash '),
        write_formula(0,B),
        write('}{'),
        write_proof(Proof),
        write('}').

 
% non-focused        
%write_proof(rule1(rp,_,_,Proof)) :-
%        write_proof(Proof).

write_proof(rule1(R,A,B,Proof)) :-
        member(R,[fl1,fr1,box(right),dia(left),over(right),under(right),oplus(right),
                  otimes(left),oslash(left),obslash(left),rp,g1,g2,g3,g4,drp,xr1,xr2,xl1,xl2]),
        write(' \\infer['),
        write_rule(R),
        write(']{'),
        write_formula(0,A),
        write(' \\vdash '),
        write_formula(0,B),
        write('}{'),
        write_proof(Proof),
        write('}').

% Binary focused        
write_proof(rule2(R,A,B,Proof1,Proof2)) :-
        member(R,[otimes(right),oslash(right),obslash(right)]),
        write(' \\infer['),
        write_rule(R),
        write(']{'),
        write_formula(0,A),
        write(' \\vdash \\fboxx{'),
        write_formula(0,B),
        write('}}{'),nl,
        write_proof(Proof1),
        write(' & '),        
        write_proof(Proof2),
        write('}').
write_proof(rule2(R,A,B,Proof1,Proof2)) :-
        member(R,[oplus(right),over(left),under(left)]),
        write(' \\infer['),
        write_rule(R),
        write(']{\\fboxx{'),
        write_formula(0,A),
        write('} \\vdash '),
        write_formula(0,B),
        write('}{'),nl,
        write_proof(Proof1),
        write(' & '),        
        write_proof(Proof2),
        write('}').

          
% Rule labels

write_rule(xr1) :-
        write('P1').
write_rule(xr2) :-
        write('P2').

write_rule(dia):-
		write('(\\Diamond )').
write_rule(box):-
		write('(\\Box )').
		
write_rule(otimes):-
		write('(\\otimes )').
write_rule(oslash):-
		write('(\\oslash )').
write_rule(obslash):-
		write('(\\obslash )').
write_rule(oplus):-
		write('(\\oplus )').
write_rule(over):-
		write('(\\slash )').
write_rule(under):-
		write('(\\bs )').

write_rule(alpha) :-
		write('\\leftslice').
write_rule(alpha1) :-
		write('\\leftslice^{-1}').	
		
write_rule(beta) :-
		write('\\triangleright').
write_rule(beta1) :-
		write('\\triangleright^{-1}').
write_rule(gamma) :-
		write('\\triangleleft').
write_rule(gamma1) :-
		write('\\triangleleft^{-1}').	
write_rule(betaplus) :-
		write('\\blacktriangleright').
write_rule(betaplus1) :-
		write('\\blacktriangleright^{-1}').
write_rule(gammaplus) :-
		write('\\blacktriangleleft').
write_rule(gammaplus1) :-
		write('\\blacktriangleleft^{-1}').	
		
write_rule(fl) :-
		write('\\leftharpoondown').	
write_rule(fl1) :-
		write('\\leftharpoonup').	
write_rule(fr) :-
		write('\\rightharpoondown').	
write_rule(fr1) :-
		write('\\rightharpoonup').	

write_rule(SRule) :- member(SRule,[rp,drp,g1,g2,g3,g4,xl1,xl2]), write(SRule).

/* write_rule(g1) :- true.
%		write('\\delta_{\\obslash\\slash}').	
%		write('\\textbf{\\d{d}}').
write_rule(g2) :- true.
%		write('\\delta_{\\obslash\\bs}').
%		write('\\textbf{\\.{q}}').
write_rule(g3) :- true.
%		write('\\delta_{\\oslash\\bs}').
%		write('\\textbf{\\d{b}}').
write_rule(g4) :- true.
%		write('\\delta_{\\oslash\\slash}').	
%		write('\\textbf{\\.{p}}').


write_rule(rp):- true.
write_rule(drp):- true. */

write_rule(dia(right)):-
		write('(\\Diamond R)').
write_rule(dia(left)):-
		write('(\\Diamond L)').
write_rule(box(right)):-
		write('(\\Box R)').
write_rule(box(left)):-
		write('(\\Box L)').
							        
write_rule(otimes(right)):-
		write('(\\otimes R)').
write_rule(over(right)):-
		write('(\\slash R)').
write_rule(under(right)):-
		write('(\\bs R)').
write_rule(otimes(left)):-
		write('(\\otimes L)').
write_rule(over(left)):-
		write('(\\slash L)').
write_rule(under(left)):-
		write('(\\bs L)').

write_rule(oplus(right)):-
		write('(\\oplus R)').
write_rule(oslash(right)):-
		write('(\\oslash R)').
write_rule(obslash(right)):-
		write('(\\obslash R)').
write_rule(oplus(left)):-
		write('(\\oplus L)').
write_rule(oslash(left)):-
		write('(\\oslash L)').
write_rule(obslash(left)):-
		write('(\\obslash L)').
										
% Formulas

write_formula(_,I-F-J) :-
    (F = _/_;F = '$VAR'(_)),
    write('\\indexed{'),
    write(I),write('}{'),
    write_formula(_,F),
    write('}{'),write(J),write('}').
    

write_formula(N,I-F-J) :-
    F \= _/_,F \= '$VAR'(_),
    write('\\bigindexed{'),
    write(I),write('}{'),
    write_formula(N,F),
    write('}{'),write(J),
    write('}').

write_formula(_,'$VAR'(N)) :-
    get_var('$VAR'(N),Var),
    write(Var).
write_formula(_,var(VAR)) :-
        write(VAR).
    
write_formula(_,A/N) :-
		print(A),
		write('_{'),
		write_index(N), 
        write('}').
        
write_formula(N,box(A)) :-
        write(' \\Box '),
        write_formula(s(N),A).
        
write_formula(N,dia(A)) :-
        write(' \\Diamond '),
        write_formula(s(N),A).

write_formula(N,box0(A)) :-
        write(' [ '),
        write_formula(s(N),A),
        write(' ] ').
        
write_formula(N,dia0(A)) :-
        write(' \\langle '),
        write_formula(s(N),A),
        write(' \\rangle ').
       
write_formula(N,otimes(A,B)) :-
        left_bracket(N),
        write_formula(s(N),A),
        write(' \\otimes '),
        write_formula(s(N),B),
        right_bracket(N).
write_formula(N,over(A,B)) :-
        left_bracket(N),
        write_formula(s(N),A),
        write('/ '),
        write_formula(s(N),B),
        right_bracket(N).
write_formula(N,under(A,B)) :-
        left_bracket(N),
        write_formula(s(N),A),
        write(' \\bs '),
        write_formula(s(N),B),
        right_bracket(N).
        
write_formula(N,otimes0(A,B)) :-
        left_bracket(N),
        write_formula(s(N),A),
        write(' \\cdot\\otimes\\cdot '),
        write_formula(s(N),B),
        right_bracket(N).
write_formula(N,over0(A,B)) :-
        left_bracket(N),
        write_formula(s(N),A),
        write(' \\cdot\\slash\\cdot '),
        write_formula(s(N),B),
        right_bracket(N).
write_formula(N,under0(A,B)) :-
        left_bracket(N),
        write_formula(s(N),A),
        write(' \\cdot\\bs\\cdot '),
        write_formula(s(N),B),
        right_bracket(N).
        
write_formula(N,oplus(A,B)) :-
        left_bracket(N),
        write_formula(s(N),A),
        write(' \\oplus '),
        write_formula(s(N),B),
        right_bracket(N).
write_formula(N,oslash(A,B)) :-
        left_bracket(N),
        write_formula(s(N),A),
        write('\\oslash '),
        write_formula(s(N),B),
        right_bracket(N).
write_formula(N,obslash(A,B)) :-
        left_bracket(N),
        write_formula(s(N),A),
        write(' \\obslash '),
        write_formula(s(N),B),
        right_bracket(N).
        
write_formula(N,oplus0(A,B)) :-
        left_bracket(N),
        write_formula(s(N),A),
        write(' \\cdot\\oplus\\cdot '),
        write_formula(s(N),B),
        right_bracket(N).
write_formula(N,oslash0(A,B)) :-
        left_bracket(N),
        write_formula(s(N),A),
        write(' \\cdot\\oslash\\cdot '),
        write_formula(s(N),B),
        right_bracket(N).
write_formula(N,obslash0(A,B)) :-
        left_bracket(N),
        write_formula(s(N),A),
        write(' \\cdot\\obslash\\cdot '),
        write_formula(s(N),B),
        right_bracket(N).

left_bracket(0) :- write(' ').
left_bracket(s(_)) :- write('(').

right_bracket(0) :- write(' ').
right_bracket(s(_)) :- write(')').

write_index(N) :-
	show(index) -> print(N) ; true.


    