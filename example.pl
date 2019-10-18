primitive_action(turnoff(N)).
primitive_action(open).
primitive_action(close).
primitive_action(up(N)).
primitive_action(down(N)).

proc(go_floor(N), ?(current_floor(N)) # up(N) # down(N)).
proc(serve(N), [go_floor(N), turnoff(N), open, close]).
proc(serve_a_floor, pi(n, [?(next_floor(n)), serve(n)])).
proc(park, if(current_floor(0), open, [down(0), open])).

proc(control, [while(some(n, on(n)), serve_a_floor), park]).

poss(up(N), S) :- holds(current_floor(M), S), M < N.
poss(down(N), S) :- holds(current_floor(M), S), M > N.
poss(open, S).
poss(close, S).
poss(turnoff(N), S) :- holds(on(N), S).

holds(current_floor(M), do(E, S)) :- E = up(M) ; E = down(M) ;
    not(E = up(N)), not(E = down(N)), holds(current_floor(M), S).

holds(on(M), do(E, S)) :- holds(on(M), S), not(E = turnoff(M)).

holds(on(3), s0).
holds(on(5), s0).
holds(current_floor(4), s0).

holds(next_floor(N), S) :- holds(on(N), S).