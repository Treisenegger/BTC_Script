primitive_action(op_push(_)).
primitive_action(op_dup).
primitive_action(op_hash160).
primitive_action(op_equalverify).
primitive_action(op_checksig).
primitive_action(op_pick).
primitive_action(op_if).
primitive_action(op_else).
primitive_action(op_endif).
primitive_action(op_toaltstack).
primitive_action(op_fromaltstack).
primitive_action(op_depth).
primitive_action(op_drop).
primitive_action(op_roll).
primitive_action(op_checkmultisig).

poss(op_push(_), _).
poss(op_dup, S) :- holds(stack(0, _), S) ;
    holds(if_valid(VD, 0), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)) ;
    holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 0), S).
poss(op_hash160, S) :- holds(stack(0, _), S), holds(stack(P, E1), S), P1 is P + 1, not(holds(stack(P1, _), S)), hash160(_, E1) ;
    holds(if_valid(VD, 0), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)) ;
    holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 0), S).
poss(op_equalverify, S) :- holds(stack(0, _), S), holds(stack(1, _), S) ;
    holds(if_valid(VD, 0), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)) ;
    holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 0), S).
poss(op_checksig, S) :- holds(stack(0, _), S), holds(stack(1, _), S) ;
    holds(if_valid(VD, 0), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)) ;
    holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 0), S).
poss(op_pick, S) :- holds(stack(0, _), S), holds(stack(P, E), S), P1 is P + 1, not(holds(stack(P1, _), S)), integer(E), E >= 0, P > E ;
    holds(if_valid(VD, 0), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)) ;
    holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 0), S).
poss(op_if, S) :- holds(stack(0, _), S) ;
    holds(if_valid(VD, 0), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)) ;
    holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 0), S).
poss(op_else, S) :- holds(if_valid(0, _), S).
poss(op_endif, S) :- holds(if_valid(0, _), S).
poss(op_toaltstack, S) :- holds(stack(0, _), S) ;
    holds(if_valid(VD, 0), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)) ;
    holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 0), S).
poss(op_fromaltstack, S) :- holds(altstack(0, _), S) ;
    holds(if_valid(VD, 0), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)) ;
    holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 0), S).
poss(op_depth, _).
poss(op_drop, S) :- holds(stack(0, _), S) ;
    holds(if_valid(VD, 0), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)) ;
    holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 0), S).
poss(op_roll, S) :- holds(stack(0, _), S), holds(stack(P, E), S), P1 is P + 1, not(holds(stack(P1, _), S)), integer(E), E >= 0, P > E ;
    holds(if_valid(VD, 0), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)) ;
    holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 0), S).
poss(op_checkmultisig, S) :- holds(stack(0, _), S), holds(stack(P, E), S), P1 is P + 1, not(holds(stack(P1, _), S)), integer(E), E >= 0, P > E, P2 is P - E - 1, holds(stack(P2, E1), S), integer(E1), E1 >= 0, P2 > E1 - 1, E >= E1 ;
    holds(if_valid(VD, 0), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)) ;
    holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 0), S).

/* Position, Element */
holds(stack(P, E), do(A, S)) :- (not(holds(if_valid(0, _), S)) ; holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 1), S)), (
        A = op_push(E), P = 0, not(holds(stack(P, _), S)) ;
        A = op_push(E), holds(stack(P1, _), S), P is P1 + 1, not(holds(stack(P, _), S)) ;
        A = op_dup, holds(stack(P1, E), S), P is P1 + 1, not(holds(stack(P, _), S)) ;
        A = op_hash160, holds(stack(P, E1), S), P1 is P + 1, not(holds(stack(P1, _), S)), hash160(E, E1) ;
        A = op_checksig, holds(stack(P, E1), S), P1 is P + 1, holds(stack(P1, E2), S), P2 is P1 + 1, not(holds(stack(P2, _), S)), (
            sig(E1, E2), E = 1 ;
            not(sig(E1, E2)), E = 0
        ) ;
        A = op_pick, holds(stack(P, E1), S), P1 is P + 1, not(holds(stack(P1, _), S)), P2 is P - 1 - E1, holds(stack(P2, E), S) ;
        A = op_fromaltstack, holds(altstack(P1, E), S), P2 is P1 + 1, not(holds(altstack(P2, _), S)), (
            P = 0, not(holds(stack(P, _), S)) ;
            holds(stack(P3, _), S), P is P3 + 1, not(holds(stack(P, _), S))
        ) ;
        A = op_depth, E = P, (
            P = 0, not(holds(stack(P, _), S)) ;
            holds(stack(P2, _), S), P is P2 + 1, not(holds(stack(P, _), S))
        ) ;
        A = op_roll, holds(stack(P1, E1), S), P2 is P1 + 1, not(holds(stack(P2, _), S)), (
            P is P1 - 1, P3 is P - E1, holds(stack(P3, E), S) ;
            holds(stack(P3, E), S), P is P3 - 1, Pmin is P1 - E1, Pmax is P1 - 1, P3 >= Pmin, Pmax >= P3
        ) ;
        holds(stack(P, E), S), not((
            A = op_hash160, P1 is P + 1, not(holds(stack(P1, _), S)) ;
            A = op_equalverify, P1 is P + 2, not(holds(stack(P1, _), S)) ;
            A = op_checksig, P1 is P + 2, not(holds(stack(P1, _), S)) ;
            A = op_pick, P1 is P + 1, not(holds(stack(P1, _), S)) ;
            A = op_if, P1 is P + 1, not(holds(stack(P1, _), S)) ;
            A = op_toaltstack, P1 is P + 1, not(holds(stack(P1, _), S)) ;
            A = op_drop, P1 is P + 1, not(holds(stack(P1, _), S)) ;
            A = op_roll, holds(stack(P1, E1), S), P2 is P1 + 1, not(holds(stack(P2, _), S)), P3 is P + E1 + 2, P3 > P1
        ))
    ) ;
    ((
        holds(if_valid(VD, 0), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)) ;
        holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 0), S)
    ), holds(stack(P, E), S)).

holds(error, do(A, S)) :- (not(holds(if_valid(0, _), S)) ; holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 1), S)), (
        A = op_equalverify, holds(stack(P, E1), S), P1 is P + 1, holds(stack(P1, E2), S), P2 is P1 + 1, not(holds(stack(P2, _), S)), E1 \= E2
    ) ;
    holds(error, S).

/* Depth (from bottom to top, essentially position), current status */
holds(if_stack(D, CS), do(A, S)) :- A = op_if, D = 0, not(holds(if_stack(D, _), S)), holds(stack(P, E), S), P1 is P + 1, not(holds(stack(P1, _), S)), (
        E \= 0, CS = 1 ;
        E = 0, CS = 0
    ) ;
    A = op_if, holds(if_valid(VD, 1), S), D is VD + 1, not(holds(if_valid(D, _), S)), holds(if_stack(VD, 1), S), holds(stack(P, E), S), P1 is P + 1, not(holds(stack(P1, _), S)), (
        E \= 0, CS = 1 ;
        E = 0, CS = 0
    ) ;
    A = op_else, holds(if_valid(D, _), S), D1 is D + 1, not(holds(if_valid(D1, _), S)), holds(if_stack(D, CS1), S), (
        CS = 1, CS1 = 0 ;
        CS = 0, CS1 = 1
    ) ;
    holds(if_stack(D, CS), S), not((
        A = op_endif, D1 is D + 1, not(holds(if_valid(D1, _), S)) ;
        A = op_else, D1 is D + 1, not(holds(if_valid(D1, _), S))
    )).

/* Depth (from bottom to top, essentially position), valid */
holds(if_valid(VD, V), do(A, S)) :- A = op_if, VD = 0, V = 1, not(holds(if_valid(VD, _), S)) ;
    A = op_if, holds(if_valid(VD1, V1), S), VD is VD1 + 1, not(holds(if_valid(VD, _), S)), (
        V = 0, (V1 = 0 ; holds(if_stack(VD1, 0), S)) ;
        V = 1, V1 = 1, holds(if_stack(VD1, 1), S)
    ) ;
    holds(if_valid(VD, V), S), not((
        A = op_endif, VD1 is VD + 1, not(holds(if_valid(VD1, _), S))
    )).

holds(if_error, S) :- holds(if_stack(0, _), S).

holds(altstack(P, E), do(A, S)) :- (not(holds(if_valid(0, _), S)) ; holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, 1), S)), (
        A = op_toaltstack, holds(stack(P1, E), S), P2 is P1 + 1, not(holds(stack(P2, _), S)), (
            P = 0, not(holds(altstack(P, _), S)) ;
            holds(altstack(P3, _), S), P is P3 + 1, not(holds(altstack(P, _), S))
        ) ;
        holds(altstack(P, E), S), not((
            A = op_fromaltstack, P1 is P + 1, not(holds(altstack(P1, _), S))
        ))
    ) ;
    ((
        holds(if_valid(VD, 0), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)) ;
        holds(if_valid(VD, 1), S), VD1 is VD + 1, not(holds(if_valid(VD1, _), S)), holds(if_stack(VD, CS), S), CS = 0
    ), holds(altstack(P, E), S)).

hash160(pub_key_hash_A, pub_key_A).
sig(signature_A, pub_key_A).

/* PAY TO PUBKEY HASH VALIDO */
/* holds(stack(E, 0), do(op_checksig, do(op_equalverify, do(op_push(pub_key_hash_A), do(op_hash160, do(op_dup, do(op_push(pub_key_A), do(op_push(signature_A), s0)))))))). */

/* PAY TO PUBKEY HASH SIGNATURE INCORRECTA */
/* holds(stack(E, 0), do(op_checksig, do(op_equalverify, do(op_push(pub_key_hash_A), do(op_hash160, do(op_dup, do(op_push(pub_key_A), do(op_push(signature_B), s0)))))))). */

/* PAY TO PUBKEY HASH PUBKEY INCORRECTA */
/* holds(error, do(op_checksig, do(op_equalverify, do(op_push(pub_key_hash_B), do(op_hash160, do(op_dup, do(op_push(pub_key_A), do(op_push(signature_A), s0)))))))). */

/* OP_PICK TEST */
/* do([op_push(0), op_push(1), op_push(2), op_push(3), op_push(4), op_push(3), op_pick], s0, S), holds(stack(E, P), S). */
