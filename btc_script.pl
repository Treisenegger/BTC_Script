primitive_action(op_push(E)).
primitive_action(op_dup).
primitive_action(op_hash160).
primitive_action(op_equalverify).
primitive_action(op_checksig).
primitive_action(op_pick).
primitive_action(op_if).

poss(op_push(E), S).
poss(op_dup, S) :- holds(stack(E, 0), S) ;
    holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 0 ;
    holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 1, holds(if_stack(VD, CS), S), CS = 0.
poss(op_hash160, S) :- holds(stack(E, 0), S), holds(stack(E1, P), S), P1 is P + 1, not(holds(stack(E2, P1), S)), hash160(H, E1) ;
    holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 0 ;
    holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 1, holds(if_stack(VD, CS), S), CS = 0.
poss(op_equalverify, S) :- holds(stack(E1, 0), S), holds(stack(E2, 1), S) ;
    holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 0 ;
    holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 1, holds(if_stack(VD, CS), S), CS = 0.
poss(op_checksig, S) :- holds(stack(E1, 0), S), holds(stack(E2, 1), S) ;
    holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 0 ;
    holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 1, holds(if_stack(VD, CS), S), CS = 0.
poss(op_pick, S) :- holds(stack(E, 0), S), holds(stack(E1, P), S), P1 is P + 1, not(holds(stack(E2, P1), S)), integer(E1), E1 >= 0, P > E1 ;
    holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 0 ;
    holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 1, holds(if_stack(VD, CS), S), CS = 0.
poss(op_if, S) :- holds(stack(E, 0), S) ;
    holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 0 ;
    holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 1, holds(if_stack(VD, CS), S), CS = 0.

/* Element, position */
holds(stack(E, P), do(A, S)) :- (not(holds(if_valid(0, V), S)) ; holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 1, holds(if_stack(VD, CS), S), CS = 1), (
        A = op_push(E), P = 0, not(holds(stack(E1, P), S)) ;
        A = op_push(E), holds(stack(E2, P1), S), P is P1 + 1, not(holds(stack(E1, P), S)) ;
        A = op_dup, holds(stack(E, P1), S), P is P1 + 1, not(holds(stack(E1, P), S)) ;
        A = op_hash160, holds(stack(E1, P), S), P1 is P + 1, not(holds(stack(E2, P1), S)), hash160(E, E1) ;
        A = op_checksig, holds(stack(E1, P), S), P1 is P + 1, P2 is P1 + 1, holds(stack(E2, P1), S), not(holds(stack(E3, P2), S)), sig(E1, E2), E = 1 ;
        A = op_checksig, holds(stack(E1, P), S), P1 is P + 1, P2 is P1 + 1, holds(stack(E2, P1), S), not(holds(stack(E3, P2), S)), not(sig(E1, E2)), E = 0 ;
        A = op_pick, holds(stack(E1, P), S), P1 is P + 1, not(holds(stack(E2, P1), S)), P2 is P - 1 - E1, holds(stack(E, P2), S) ;
        holds(stack(E, P), S), not((
            A = op_hash160, P1 is P + 1, not(holds(stack(E1, P1), S)) ;
            A = op_equalverify, P1 is P + 2, not(holds(stack(E1, P1), S)) ;
            A = op_checksig, P1 is P + 2, not(holds(stack(E1, P1), S)) ;
            A = op_pick, P1 is P + 1, not(holds(stack(E1, P1), S)) ;
            A = op_if, P1 is P + 1, not(holds(stack(E1, P1), S))
        ))
    ) ;
    ((
        holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 0 ;
        holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 1, holds(if_stack(VD, CS), S), CS = 0
    ), holds(stack(E, P), S)).

holds(error, do(A, S)) :- ((not(holds(if_valid(0, V), S)) ; holds(if_valid(VD, V), S), VD1 is VD + 1, not(holds(if_valid(VD1, V1), S)), V = 1, holds(if_stack(VD, CS), S), CS = 1),
    A = op_equalverify, holds(stack(E1, P), S), P1 is P + 1, P2 is P1 + 1, holds(stack(E2, P1), S), not(holds(stack(E3, P2), S)), E1 \= E2) ;
    holds(error, S).

/* Depth (from bottom to top, essentially position), condition evaluation, current status */
holds(if_stack(D, CS), do(A, S)) :- A = op_if, D = 0, not(holds(if_stack(D, CS1), S)), holds(stack(E, P), S), P1 is P + 1, not(holds(stack(E1, P1), S)), (
        E \= 0, CS = 1 ;
        E = 0, CS = 0
    ) ;
    A = op_if, V = 1, holds(if_valid(VD, V), S), D is VD + 1, not(holds(if_valid(D, V1), S)), CS1 = 1, holds(if_stack(VD, CS1), S), holds(stack(E, P), S), P1 is P + 1, not(holds(stack(E1, P1), S)), (
        E \= 0, CS = 1 ;
        E = 0, CS = 0
    ) ;
    holds(if_stack(D, CS), S).

/* Depth (from bottom to top, essentially position), valid */
holds(if_valid(VD, V), do(A, S)) :- A = op_if, VD = 0, V = 1, not(holds(if_valid(VD, V1), S)) ;
    A = op_if, holds(if_valid(VD1, V1), S), VD is VD1 + 1, not(holds(if_valid(VD, V2), S)), (
        V = 0, (V1 = 0 ; CS = 0, holds(if_stack(VD1, CS), S)) ;
        V = 1, V1 = 1, CS = 1, holds(if_stack(VD1, CS), S)
    ) ;
    holds(if_valid(VD, V), S).

holds(if_error, S) :- holds(if_stack(0, CS), S).

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
