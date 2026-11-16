% termproof: termination proofs for Detlog-style predicates. A predicate terminates if some
% argument gets strictly smaller in every recursive call: either the call's argument is a
% proper subterm of the head's (a list's tail, say), or it is N - 1 for a number guarded by
% N > 0. termproof finds such an argument and returns it as the certificate; a predicate with
% no such argument gets no certificate (it may loop).
% A predicate is Name-Clauses, clauses as (Head :- Body).
%?- certify(len, C).           % C = decreases(1): the list argument shrinks
%?- certify(countdown, C).     % C = decreases(1): N - 1 with N > 0
%?- certify(loop, C).          % C = none
%?- run(len, len([a,b,c], N), 100, R).   % R = finished
:- module(termproof, [pred/2, certify/2, recursive_calls/3, run/4, decreases/4]).
:- use_module(library(lists)).
:- use_module(library(apply)).

pred(len, [ (len([], 0) :- true), (len([_|T], N) :- len(T, M), N is M + 1) ]).
pred(app, [ (app([], L, L) :- true), (app([H|T], L, [H|R]) :- app(T, L, R)) ]).
pred(countdown, [ (countdown(0, []) :- true), (countdown(N, [N|T]) :- N > 0, M is N - 1, countdown(M, T)) ]).
pred(tree_size, [ (size(leaf, 0) :- true), (size(node(L, R), S) :- size(L, A), size(R, B), S is A + B + 1) ]).
pred(loop, [ (loop(X) :- loop(X)) ]).
pred(grow, [ (grow(X) :- grow([X])) ]).
pred(swap_args, [ (sw([], _) :- true), (sw([_|T], L) :- sw(L, T)) ]).   % shrinks in neither argument on every call

% recursive_calls(+Clause, +Functor/Arity, -Calls): the head and its recursive calls (with guards seen before them).
recursive_calls((H :- B), F/A, H-Calls) :- body_list(B, Gs), findall(C-Before, ( append(Before, [C|_], Gs), functor(C, F, A) ), Calls).
body_list((A, B), L) :- !, body_list(A, La), body_list(B, Lb), append(La, Lb, L).
body_list(true, []) :- !.
body_list(G, [G]).

% decreases(+Head, +Call, +Before, +I): argument I is smaller in the call than in the head.
decreases(H, C, Before, I) :- arg(I, H, X), arg(I, C, Y), ( proper_subterm(Y, X) -> true ; nat_step(X, Y, Before) ).
proper_subterm(Y, X) :- compound(X), X =.. [_|As], member(A, As), ( A == Y -> true ; proper_subterm(Y, A) ), !.
nat_step(X, Y, Before) :- var(X), member(G, Before), G = (Y0 is E), Y0 == Y, E = (X0 - 1), X0 == X, member(G2, Before), G2 = (X1 > 0), X1 == X, !.

% certify(+Pred, -Certificate): decreases(I) for the first argument that shrinks in every recursive call, or none.
certify(P, C) :- pred(P, Cs), Cs = [C0|_], copy_term(C0, (H0 :- _)), functor(H0, F, A),
    (   between(1, A, I), forall(( member(Cl, Cs), copy_term(Cl, Cl2), recursive_calls(Cl2, F/A, H-Calls), member(Call-Before, Calls) ), decreases(H, Call, Before, I))
    ->  C = decreases(I)
    ;   C = none ).

% run(+Pred, +Goal, +Depth, -Result): finished (every solution found within Depth) or out_of_depth.
run(P, G, D, R) :- pred(P, Cs), catch(( forall(solve(Cs, G, D), true), R0 = finished ), depth, R0 = out_of_depth), R = R0.
solve(_, true, _) :- !.
solve(Cs, (A, B), D) :- !, solve(Cs, A, D), solve(Cs, B, D).
solve(_, G, _) :- predicate_property(system:G, built_in), !, call(G).
solve(Cs, G, D) :- ( D =< 0 -> throw(depth) ; true ), D1 is D - 1, member(C, Cs), copy_term(C, (H :- B)), H = G, solve(Cs, B, D1).
