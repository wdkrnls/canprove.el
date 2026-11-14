# can-prove

A propositional-logic checker for Emacs Lisp. It decides whether a set of premises entails a conclusion, and — when they don't — returns a concrete counterexample. It's a small tool in the spirit of `canProve` from yacas, scoped to qualitative (propositional) arguments only: no arithmetic, no quantifiers, no algebra, just connectives and truth.

## What it does

- **Validity checking.** `(can-prove premises conclusion)` returns :valid `1` or `0`.
- **Counterexamples.** `(can-prove-counterexample ...)` returns either `:valid` or the list of atoms that are true in a falsifying assignment. The empty list `()` is a legitimate result meaning "all atoms false."
- **A readable infix notation.** Write arguments as strings with `*`/`+` for and/or (Jaynes-style), ASCII or Unicode operators, and `.`/`,`-separated premises.
- **Explanations.** `can-prove-explain` echoes the argument in normalized notation and prints the counterexample as `p=f, q=t`.

It uses two strategies behind one API: a bit-vector truth-table evaluator (fast for up to ~20 atoms) and a Tseitin + memoized DPLL SAT solver (scales further). The switchover is governed by `can-prove-bitvec-threshold`.

## Requirements

Emacs 27 or later (the bit-vector backend relies on bignums; 28+ is more comfortable). Dependencies: `seq.el` and `subr-x` — no `cl-lib`.

## Installation

Put `can-prove.el` on your `load-path` and:

```elisp
(require 'can-prove)
```

## Quick start

```elisp
(can-prove '((implies p q) p) 'q)              ; => t        (modus ponens)
(can-prove-counterexample '((implies p q)) 'q) ; => ()       (p=0, q=1)
(can-prove-counterexample '((implies p q) q) 'p) ; => (q)    (p=1, q=1)
(can-prove-tautology '(or p (not p)))          ; => t        (excluded middle)
```

Or write it as a string:

```elisp
(can-prove-argument "p -> q. p. therefore q.")  ; => :valid
(can-prove-argument "p -> q. q. therefore p.")  ; => (q)
(can-prove-string "p + ¬p")                     ; => :valid
```

And get an explanation:

```elisp
(can-prove-explain-argument "p => q. q. therefore p.")
;; =>
;; p ⊃ q, q  ⊢  p
;; Invalid — counterexample: p=f, q=t.
```

## Notation

Connectives, with `¬` binding tightest and `≡` loosest:

| Meaning | Spellings |
|---|---|
| not | `¬` `~` `!` `-` `not` |
| and | `*` `∧` `&&` `/\` `&` `and` |
| or | `+` `∨` `||` `\/` `\|` `or` |
| implies | `⊃` `->` `=>` `→` `then` `implies` |
| iff | `≡` `<=>` `<->` `↔` `iff` `equiv` |
| xor | `⊕` `xor` |

Details:

- **Precedence:** `¬` > `*` > `+`/`⊕` > `⊃` (right-associative) > `≡`.
- **Juxtaposition** means conjunction: `p q` is `p * q`, and `¬p q` is `¬p * q`.
- **Literals** `true` and `false` are accepted; atoms are `[A-Za-z_][A-Za-z0-9_]*` (case-insensitive, interned lowercased).
- **Premises** in an argument string are separated by `,`, `;`, or `.`.
- **Turnstiles:** `|-`, `⊢`, `⊨`, `∴`, `therefore`, `hence`, `⟹`.

## API

| Function | Purpose |
|---|---|
| `can-prove` | `t` if premises entail conclusion |
| `can-prove-counterexample` | `:valid`, or a list of true atoms in a falsifying assignment |
| `can-prove-tautology` | `t` if a single formula is valid |
| `can-prove-parse` | infix string → S-expression |
| `can-prove-string` | check a single formula given as a string |
| `can-prove-argument` | check an argument string |
| `can-prove-explain` | explain an argument given as S-expressions |
| `can-prove-explain-argument` | explain an argument given as a string |

Customization: `can-prove-bitvec-threshold` (default `20`) — the atom count above which the SAT backend is used. Set it very high to force bit-vector, or `-1` to force SAT (useful in tests).

## Tests

```sh
emacs -batch -L . -l can-prove-tests.el -f ert-run-tests-batch-and-exit
```

The suite checks the parser, the validity and counterexample results, and both backends against an independent brute-force oracle, including a randomized property test that cross-checks bit-vector, DPLL, and truth-table semantics.

## Limitations

- **Propositional only.** No quantifiers, predicates, equality, or arithmetic. For those you'd want to delegate to Emacs Calc or an external solver.
- **Exponential in the worst case.** The bit-vector backend is `O(2^n)` bits; memoized DPLL is exponential too, though it exploits shared subproblems and is usually far faster on structured inputs.
- **One counterexample, not all of them.** The returned assignment is genuine but not minimized — it may assign atoms that are irrelevant to the failure.
- **Rendering round-trips are equivalent, not identical.** `can-prove--render` may emit more parentheses than strictly necessary, so re-parsing a rendered formula yields an equivalent tree, not always a structurally equal one.

## License

GPL 3+
