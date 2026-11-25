% Theorems, proved by exhaustion. Run: swipl -g main -t halt proofs/theorems.pl
:- module(theorems, [main/0]).
:- use_module(prove).
:- discontiguous theorem/1.
:- use_module(library(lists)).
:- use_module(library(apply)).
main :- prove_all(theorems).
:- use_module('../prolog/termproof').

% Domain: every predicate, run on every input of size up to 4 in its first argument.
input(len, len(L, _)) :- between(0, 4, N), length(L, N).
input(app, app(L, [x], _)) :- between(0, 4, N), length(L, N).
input(countdown, countdown(N, _)) :- between(0, 4, N).
input(tree_size, size(T, _)) :- tree(3, T).
input(loop, loop(a)).
input(grow, grow(a)).
input(swap_args, sw(L, M)) :- between(0, 2, N), length(L, N), between(0, 2, K), length(M, K).
tree(_, leaf).
tree(D, node(L, R)) :- D > 0, D1 is D - 1, tree(D1, L), tree(D1, R).
size_of(len(L, _), N) :- length(L, N).
size_of(app(L, _, _), N) :- length(L, N).
size_of(countdown(N, _), N).
size_of(size(T, _), N) :- term_size_(T, N).
size_of(sw(A, B), N) :- length(A, X), length(B, Y), N is X + Y.
term_size_(leaf, 0).
term_size_(node(L, R), N) :- term_size_(L, A), term_size_(R, B), N is A + B + 1.

% 1. Sound: a certified predicate finishes on every input (its named arguments given), within a depth of its input's size plus 2.
theorem(certified_predicates_terminate) :-
    forall(( pred(P, _), certify(P, C), C \== none, input(P, G), size_of(G, S) ), ( D is S + 2, run(P, G, D, finished) )).

% 2. The looping predicates get no certificate (and really don't finish).
theorem(loops_are_not_certified) :- forall(member(P, [loop, grow]), ( certify(P, none), input(P, G), run(P, G, 50, out_of_depth) )).

% 3. The expected certificates.
theorem(known_certificates) :- certify(len, decreases(1)), certify(app, decreases(1)), certify(countdown, decreases(1)), certify(tree_size, decreases(1)), certify(swap_args, decreases_sum([1, 2])).

% 4. A certificate names an argument that really shrinks: in every recursive call it is a proper part of the head's, or N - 1 of N > 0;
% a sum certificate names arguments whose total size shrinks in every call.
theorem(certificates_are_checkable) :-
    forall(( pred(P, Cs), certify(P, decreases(I)), member(C, Cs), C = (H0 :- _), functor(H0, F, A), recursive_calls(C, F/A, Calls), member(H-Call-Before, Calls) ), decreases(H, Call, Before, I)),
    forall(( pred(P, Cs), certify(P, decreases_sum(S)), member(C, Cs), C = (H0 :- _), functor(H0, F, A), recursive_calls(C, F/A, Calls), member(H-Call-_, Calls) ), sum_decreases(H, Call, S)).
