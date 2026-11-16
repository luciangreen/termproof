# termproof

termination proofs for Detlog-style predicates. A predicate terminates if some argument gets strictly smaller in every recursive call: either the call's argument is a proper subterm of the head's (a list's tail, say), or it is N - 1 for a number guarded by N > 0. termproof finds such an argument and returns it as the certificate; a predicate with no such argument gets no certificate (it may loop). A predicate is Name-Clauses, clauses as (Head :- Body).

## Use

```prolog
?- use_module(prolog/termproof).
?- certify(len, C).           % C = decreases(1): the list argument shrinks
?- certify(countdown, C).     % C = decreases(1): N - 1 with N > 0
?- certify(loop, C).          % C = none
?- run(len, len([a,b,c], N), 100, R).   % R = finished
```

## Proofs

`proofs/theorems.pl` proves 4 theorems by exhaustion: each one is checked for every case in a finite domain that covers every branch of the definitions. every predicate, run on every input of size up to 4 in its first argument.

1. Sound: a certified predicate finishes on every input, within a depth of its input's size plus 2.
2. The looping predicates get no certificate (and really don't finish).
3. The expected certificates.
4. A certificate names an argument that really shrinks: in every recursive call it is a proper part of the head's, or N - 1 of N > 0.

```sh
swipl -g main -t halt proofs/theorems.pl
```

## 200 inputs and outputs

`io/ios.txt` lists 200 inputs and outputs from real runs, and `io/ios.pl` has the same as Prolog facts. The inputs come from a fixed seed (`io/cases.pl`). `swipl -g check -t halt io/run.pl` runs them again. It fails if any output changes, or if a predicate doesn't confirm its own recorded output, which checks steadfastness. GitHub Actions runs the proofs and the examples on every push, and records the examples on the first push.

Licence: BSD-3-Clause.
