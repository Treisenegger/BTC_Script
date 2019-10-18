primitive_action(op_push(E)).
primitive_action(op_dup).
primitive_action(op_hash160).
primitive_action(op_equalverify).
primitive_action(op_checksig).
primitive_action(op_pick).
primitive_action(op_if).

poss(op_push(E), S).
poss(op_dup, S) :- holds(stack(E, 0), S).
poss(op_hash160, S) :- holds(stack(E, 0), S), holds(stack(E1, P), S), P1 is P + 1, not(holds(stack(E2, P1), S)), hash160(H, E1).
poss(op_equalverify, S) :- holds(stack(E1, 0), S), holds(stack(E2, 1), S).
poss(op_checksig, S) :- holds(stack(E1, 0), S), holds(stack(E2, 1), S).
poss(op_pick, S) :- holds(stack(E, 0), S), holds(stack(E1, P), S), P1 is P + 1, not(holds(stack(E2, P1), S)), integer(E1), E1 >= 0, P > E1.
poss(op_if, S) :- holds(stack(E, 0), S).

/* Element, position */
holds(stack(E, P), do(A, S)) :- A = op_push(E), P = 0, not(holds(stack(E1, P), S)) ;
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
        A = op_pick, P1 is P + 1, not(holds(stack(E1, P1), S))
    )).

holds(error, do(A, S)) :- A = op_equalverify, holds(stack(E1, P), S), P1 is P + 1, P2 is P1 + 1, holds(stack(E2, P1), S), not(holds(stack(E3, P2), S)), not(E1 = E2) ;
    holds(error, S).

/* Depth (from bottom to top, essentially position), condition evaluation, current status */
holds(if_stack(D, CE, CS), do(A, S)) :- A = op_if, D = 0, CS = 1, not(holds(if_stack(D, CE1, CS1), S)), holds(stack(E, P), S), P1 is P + 1, not(holds(stack(E1, P1), S)), E \= 0, CE = 1 ;
    A = op_if, D = 0, CS = 1, not(holds(if_stack(D, CE1, CS1), S)), holds(stack(E, P), S), P1 is P + 1, not(holds(stack(E1, P1), S)), E = 0, CE = 0 ;
    A = op_if, CS = 1, holds(if_stack(D1, CE1, CS1), S), D is D1 + 1, not(holds(if_stack(D, CE2, CS2), S)), holds(stack(E, P), S), P1 is P + 1, not(holds(stack(E1, P1), S)), E \= 0, CE = 1 ;
    A = op_if, CS = 1, holds(if_stack(D1, CE1, CS1), S), D is D1 + 1, not(holds(if_stack(D, CE2, CS2), S)), holds(stack(E, P), S), P1 is P + 1, not(holds(stack(E1, P1), S)), E = 0, CE = 0 ;
    holds(if_stack(D, CE, CS), S).

holds(if_error, S) :- holds(if_stack(0, CE, CS), S).

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
