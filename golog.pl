:- op(950, xfy, [#]).
do([], S, S).
do([E | L], S, S1) :- do(E,S,S2), do(L,S2,S1).
do(?(P),S,S) :- holds(P,S).
do(E1 # E2,S,S1) :- do(E1,S,S1) ; do(E2,S,S1).
do(if(P,E1,E2),S,S1) :- do([?(P),E1] # [?(neg(P)),E2],S,S1).
do(star(E),S,S1) :- do([] # [E,star(E)],S,S1).
do(while(P,E),S,S1) :- do([star([?(P),E]),?(neg(P))],S,S1).
do(pi(V,E),S,S1) :- sub(V,_,E,E1), do(E1,S,S1).
/* do(E,S,S1) :- proc(E,E1), do(E1,S,S1). */
do(E,S,do(E,S)) :- primitive_action(E), poss(E,S).

sub(X1,X2,T1,T2) :- var(T1), T2 = T1.
sub(X1,X2,T1,T2) :- not(var(T1)), T1 = X1, T2 = X2.
sub(X1,X2,T1,T2) :- not(T1 = X1), T1 =..[F|L1], sub_list(X1,X2,L1,L2), T2 =..[F|L2].
sub_list(X1,X2,[],[]).
sub_list(X1,X2,[T1|L1],[T2|L2]) :- sub(X1,X2,T1,T2), sub_list(X1,X2,L1,L2).

holds(and(P1,P2),S) :- holds(P1,S), holds(P2,S).
holds(or(P1,P2),S) :- holds(P1,S); holds(P2,S).
holds(neg(P),S) :- not(holds(P,S)).
holds(some(V,P),S) :- sub(V,_,P,P1), holds(P1,S).