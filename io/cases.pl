:- module(cases, [title/1, case/3]).
:- use_module('../prolog/termproof').
:- use_module(engine).
title('termproof').
pred_g(P) :- rnd_pick([len, app, countdown, tree_size, loop, grow, swap_args], P).
case(certify, [P], certify) :- pred_g(P).
case(run_len, [len(L, _), D], run_len) :- rnd_int(0, 8, N), length(L, N), maplist(=(a), L), rnd_int(1, 12, D).
case(run_countdown, [countdown(N, _), D], run_countdown) :- rnd_int(0, 9, N), rnd_int(1, 12, D).
case(run_loop, [D], run_loop) :- rnd_int(1, 30, D).
run_len(G, D, R) :- run(len, G, D, R).
run_countdown(G, D, R) :- run(countdown, G, D, R).
run_loop(D, R) :- run(loop, loop(a), D, R).
