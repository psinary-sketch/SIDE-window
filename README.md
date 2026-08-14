# SIDE-window

**Lemma A, the window arithmetic, and the window ladder — as decidable statements about small naturals.**

Vanilla Lean 4 (`v4.29.1`). **No Mathlib, no Batteries, no dependencies of any kind.** Every theorem is
closed by `decide`, so the whole library is checkable by the Lean kernel alone, and every terminal is
**fully axiom-free** — not `{propext, Classical.choice, Quot.sound}`, but *no axioms at all*.

```
$ lake build && lake env lean AxiomCheck.lean
'SIDEWindow.lemmaA' does not depend on any axioms
... (11 terminals, all the same)
```

## What is in here

| terminal | statement |
|:--|:--|
| `lemmaA` | `primePowersLE 2 = [2]` |
| `lemmaA_count` | exactly one prime power is `≤ 2` |
| `window_prime_free` | `primePowersLT 2 = []` — the window `(1/2, 2)` carries no prime power |
| `window_one_prime` | `primePowersLT 3 = [2]` — the window `(1/3, 3)` carries exactly one |
| `window_four_has_two` | `primePowersLT 4 = [2, 3]` |
| `window_two_is_maximal_prime_free` | nothing below `2`; something below `3` |
| `window_three_is_maximal_one_prime` | count below `3` is `1`; count below `4` is `2` |
| `primePower_counts` | the counting function tabulated on `2 … 10` |
| `primePowers_below_ten` | `[2, 3, 4, 5, 7, 8, 9]` — `6` is absent, being `2 · 3` |
| `isPrime_examples`, `isPrimePower_examples` | the definitions pinned by examples |

## WHAT THIS KERNEL DOES NOT CLAIM

**Read this before citing anything here.** The same list is carried in the module docstring, so it
travels with the source.

* **It proves nothing about ζ, about `h2`, or about any operator inequality.** This is elementary
  counting of prime powers below small bounds. **Nothing here bears on the sign of `W_∞ − W_2`**, and no
  result may be cited as evidence about it.

* **It proves nothing about real intervals.** The corpus states Lemma A as *"for `λ² ∈ (2,3)` the prime
  side has exactly one term, `p^k = 2`"* — a statement quantifying over a real interval. This library
  proves **the arithmetic residue only**: the prime powers `n ≤ 2` are exactly `[2]`. The step from
  `λ² ∈ (2,3)` to the bound `2` is the observation that a prime power is a natural number and a natural
  number `< 3` is `≤ 2`. **That step is one line of ordinary mathematics and it is not formalized here.**

* **The windows are half-vacuous, and saying so is part of the result.** The corpus writes them
  multiplicatively as `(1/2, 2)` and `(1/3, 3)`. Every prime power is `≥ 2 > 1 ≥ 1/L`, so **the lower
  endpoint never binds**: the whole content lives in the upper bound, and the theorems are stated as
  counts below an integer bound, which is what they are.

* **Maximality over real `L` is not proved.** The two maximality terminals establish maximality **at
  integer bounds only**. Extending to real `L` uses that `L ↦ #{prime powers < L}` is a step function
  jumping exactly at prime powers, hence constant between consecutive ones. **That argument is standard
  and is not in this repository.**

* **`IsPrime` here is trial division, defined in this file.** It is not Mathlib's `Nat.Prime`, and no
  lemma about it is imported or assumed.

## The δ/L law is deliberately absent

The corpus's `δ/L` law — Φ's negative fraction `= 1 − log 2 / log L`, measured at bank over
`L ∈ {2.2, 2.5, 3.0, 3.5, 4.0}` — is a **conjecture with a measured table**. It is `MEASURED-AT-BANK`,
**never proved**, and its two largest rows (`L = 3.5`, `L = 4.0`) extrapolate past the `(1,3]` range that
Lemma 5.2's un-run re-derivation would cover.

**It appears in this repository only as a comment.** There is no definition, no statement and no theorem
about it — because a Lean file containing a *name* for it would invite a citation it cannot support. It
stays in `THE_ATTEMPT_RECORD`, where it is graded.

## The ladder (`v0.2`, `SIDEWindow/Ladder.lean`)

`v0.1` proved the prime-free window `(1/2, 2)` and the one-prime window `(1/3, 3)`. `v0.2` adds the rung
above them and the counting function that generates all three.

| terminal | statement |
|:--|:--|
| `window_two_prime` | `primePowersLT 4 = [2, 3]` — the window `(1/4, 4)` carries exactly two |
| `window_four_is_maximal_two_prime` | `W 4 = 2 ∧ W 5 = 3` |
| `the_window_ladder` | `W 2 = 0 ∧ W 3 = 1 ∧ W 4 = 2 ∧ W 5 = 3` — the three windows in one statement |
| `W_table_low` · `W_table_mid` | `W` tabulated on the rungs `2 … 18` |
| `W_flat_at_six` | `W 6 = W 7` — the first composite that is not a prime power is where the count first fails to advance |
| `W_flat_run_at_fourteen` | `W 14 = W 15 = W 16` — the first flat run of two |
| `primePowers_below_eighteen` | `[2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17]` |

### **`W` HAS NOTHING TO DO WITH THE CORPUS'S `W_2` / `W_∞`**

`W n` counts prime powers below `n`. **The name collision is unfortunate and is flagged in the module
docstring as well as here**, because `W_2` and `W_∞` are the corpus's windowed quantities and **nothing in
this repository bears on the sign of `W_∞ − W_2`.**

**`W` is tabulated, not characterized.** No closed form, no asymptotic, no growth statement is proved or
implied — in particular nothing here is a Chebyshev or prime-counting estimate. That the count is constant
between consecutive prime powers is *visible* in the table and is **not** proved as a general statement;
it is exactly the step needed to lift maximality from integer bounds to real `L`, and it is not taken here.

## Provenance

Sized as the smallest real Lean target of the Phase-2 board, built 2026-08-14; the ladder added the same day as `v0.2`.

**Self-contained by construction:** every definition and every theorem used is written in this
repository. It imports nothing beyond Lean 4 core, draws on no private repository, and reproduces no
material from anywhere else in the programme. **Nothing here deposits.**

## Build

```
lake build
lake env lean AxiomCheck.lean
```
