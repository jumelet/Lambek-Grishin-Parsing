/*=====================================================
                    Sample lexicon
=====================================================*/
% Semantic terms are ignored, but could be added here.
                
lex(alice, np).
lex(bob, np).

lex(that, over(under(n, n),over(s, dia(box(np))))).
lex(about, over(under(n, n),np)).
lex(everyone, otimes(over(np, n),n)).
lex(someone, otimes(over(np, n),n)).
lex(some, over(np, n)).
lex(every, over(np, n)).
lex(teacher, n).
lex(student, n).
lex(unicorn, n).
lex(left, under(np, s)).
lex(likes, over(under(np, s),np)).
lex(thinks, over(under(np, s),s)).
lex(someone2, obslash(oslash(s, s),np)).
lex(everyone2, over(s, under(np, s))). 
lex(today,under(under(np,s),under(np,s))).
lex(and,over(under(s,s),s)).
lex(beautiful,over(n,n)).
lex(blue,over(n,n)).
lex(sky,n).

lex(seems_to,over(under(np,s),under(np,sinf))).
lex(walk,under(over(under(np,s),under(np,sinf)),under(np,s))).
lex(walk2,under(np,sinf)).