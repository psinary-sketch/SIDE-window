/-
  SIDE-window · Apex.lean
  =======================

  THE APEX AT THE SQUARE: for each prime `p`, the number `p²` plays two roles at once,
  and this file compiles the arithmetic half of that coincidence.

  Vanilla Lean 4. No Mathlib, no Batteries, no dependencies. Every theorem is closed by
  `decide` or by one core rewrite, so the whole file is checkable by the Lean kernel alone.

  ── THE COINCIDENCE, STATED BEFORE ANYTHING IS CLAIMED ──────────────────────────

  Fix a prime `p` and consider the one-prime-`p` lag form on a window of length `log L`.

    ROLE 1 — THE BRANCH TURN.  The lag is `log p`; the room left over is `log L − log p`.
             They are equal exactly when `log L = 2 log p`, i.e. exactly at `L = p²`.

    ROLE 2 — THE SECOND LADDER RUNG.  The powers of `p` are `p, p², p³, …`. The second
             of them is `p²`, and it is the next one to enter a growing window.

  The two roles name THE SAME NUMBER. That is the coincidence.

  ── WHAT THIS FILE COMPILES, AND IT IS ONLY THE ARITHMETIC ──────────────────────

  READ THIS BEFORE CITING ANYTHING HERE.

  * IT COMPILES THE ARITHMETIC COINCIDENCE ONLY: that `p² = p · p`, that exactly one
    power of `p` lies strictly below `p²`, and that exactly two lie at or below it, so
    `p²` is the second rung. THAT IS ALL.

  * IT PROVES NOTHING ANALYTIC. That the negative-direction count of the operator `Φ`
    actually turns at `L = p²` is a MEASURED statement about a discretized bench, filed
    `MEASURED-AT-BANK` in the corpus. It is NOT proved here and nothing here is evidence
    for it. There is deliberately no definition of `Φ`, no negative count, and no `δ/L`
    law anywhere in this repository.

  * ROLE 1 IS NOT FORMALIZED. The step "lag equals room exactly at `L = p²`" is a
    statement about real logarithms. This file contains no logarithms and no reals. The
    step is one line of ordinary mathematics and A READER WHO WANTS IT MUST SUPPLY IT.

  * THE GENERAL `p` IS PROVED FOR ONE FACT ONLY. `turn_is_square` holds for every
    natural `p` and is proved by core rewriting. Every OTHER theorem below is `decide`
    on a CONCRETE `p ∈ {2, 3, 5, 7, 11, 13}`. THERE IS NO INDUCTION AND NO GENERAL
    STATEMENT ABOUT ALL PRIMES, because `decide` cannot give one and this repository
    imports nothing that could.

  * THE ONE-PRIME LADDER IS NOT THE WINDOW. `pPowersLT p x` counts powers of `p` alone.
    A real window of length `log L` contains the powers of EVERY prime below `L`, which
    is `primePowersLT` from `Window.lean`. The two differ: at `L = 4` the `2`-ladder
    gives `[2]` while the full window gives `[2, 3]`. `apex_ladder_is_not_window` states
    that difference as a theorem so it cannot be glossed over.

  * IT PROVES NOTHING ABOUT ζ, ABOUT `h2`, OR ABOUT ANY OPERATOR INEQUALITY, and nothing
    here bears on the sign of `W_∞ − W_2`.
-/

import SIDEWindow.Window

namespace SIDEWindow

/-! ## Powers of a single prime, by repeated division

`isPowerAux p fuel n` divides `n` by `p` while it divides evenly and reports whether the
result reaches `1`. The fuel is structural, so the definition is obviously terminating;
calling it with `fuel = n` is always enough, since each step at least halves `n`. -/

def isPowerAux (p : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, n =>
      if n == 1 then true
      else if p ≥ 2 && n % p == 0 then isPowerAux p fuel (n / p)
      else false

/-- `IsPowerOf p n` holds when `n = p ^ k` for some `k ≥ 1`. The `2 ≤ n` clause is what
excludes `k = 0`; `1` is a power of every base and is never a ladder rung here. -/
def IsPowerOf (p n : Nat) : Bool :=
  decide (2 ≤ p) && decide (2 ≤ n) && isPowerAux p n n

/-- Pinned by examples, so the definition is fixed by more than its text. -/
theorem isPowerOf_examples :
    IsPowerOf 2 2 = true ∧ IsPowerOf 2 4 = true ∧ IsPowerOf 2 8 = true ∧
    IsPowerOf 2 6 = false ∧ IsPowerOf 2 1 = false ∧
    IsPowerOf 3 9 = true ∧ IsPowerOf 3 27 = true ∧ IsPowerOf 3 6 = false ∧
    IsPowerOf 5 25 = true ∧ IsPowerOf 5 10 = false := by decide

/-- The powers of `p` strictly below `x`, in increasing order. -/
def pPowersLT (p x : Nat) : List Nat := (List.range x).filter (IsPowerOf p)

/-- The powers of `p` at most `x`, in increasing order. -/
def pPowersLE (p x : Nat) : List Nat := (List.range (x + 1)).filter (IsPowerOf p)

/-! ## Role 1's arithmetic residue: the turn bound is the square

The only general statement in this file. It says nothing about logarithms or about any
operator; it records that the number named by "the square of the lag base" is `p · p`.

PROVED IN TERM MODE ON PURPOSE. The obvious `by rw [Nat.pow_succ, Nat.pow_one]` compiles
and is correct, and it costs `propext` — `rw` goes through `Eq.mpr`. That one tactic would
have ended this repository's headline property, which is that NOTHING here depends on any
axiom at all. It was caught by `AxiomCheckApex.lean` on its first run, which is the
instrument this repository exists to run. -/

theorem turn_is_square (p : Nat) : p ^ 2 = p * p :=
  congrArg (fun x => x * p) (Nat.one_mul p)

/-! ## Role 2: `p²` is the second rung, and it is not yet in the window at `L = p²`

For each concrete prime, exactly ONE power of `p` lies strictly below `p²` — namely `p`
itself — and exactly TWO lie at or below it. So `p²` is the second rung of the `p`-ladder
and it is the next rung to enter a window growing past `L = p²`. -/

theorem apex_2  : pPowersLT 2 (2 ^ 2) = [2] ∧ pPowersLE 2 (2 ^ 2) = [2, 4] := by decide
theorem apex_3  : pPowersLT 3 (3 ^ 2) = [3] ∧ pPowersLE 3 (3 ^ 2) = [3, 9] := by decide
theorem apex_5  : pPowersLT 5 (5 ^ 2) = [5] ∧ pPowersLE 5 (5 ^ 2) = [5, 25] := by decide
theorem apex_7  : pPowersLT 7 (7 ^ 2) = [7] ∧ pPowersLE 7 (7 ^ 2) = [7, 49] := by decide
theorem apex_11 : pPowersLT 11 (11 ^ 2) = [11] ∧ pPowersLE 11 (11 ^ 2) = [11, 121] := by decide
theorem apex_13 : pPowersLT 13 (13 ^ 2) = [13] ∧ pPowersLE 13 (13 ^ 2) = [13, 169] := by decide

/-- The same six statements as counts: one rung strictly below the turn bound, two at or
below it. This is the sentence "`p²` is the SECOND `p`-power", made checkable. -/
theorem apex_counts :
    (pPowersLT 2 (2 ^ 2)).length = 1 ∧ (pPowersLE 2 (2 ^ 2)).length = 2 ∧
    (pPowersLT 3 (3 ^ 2)).length = 1 ∧ (pPowersLE 3 (3 ^ 2)).length = 2 ∧
    (pPowersLT 5 (5 ^ 2)).length = 1 ∧ (pPowersLE 5 (5 ^ 2)).length = 2 ∧
    (pPowersLT 7 (7 ^ 2)).length = 1 ∧ (pPowersLE 7 (7 ^ 2)).length = 2 ∧
    (pPowersLT 11 (11 ^ 2)).length = 1 ∧ (pPowersLE 11 (11 ^ 2)).length = 2 ∧
    (pPowersLT 13 (13 ^ 2)).length = 1 ∧ (pPowersLE 13 (13 ^ 2)).length = 2 := by decide

/-- The turn bound is exactly the entry point: one rung below `p²`, two below `p² + 1`.
So the rung count on the `p`-ladder increments exactly as the window passes `p²`. -/
theorem apex_is_the_entry_point :
    (pPowersLT 2 (2 ^ 2)).length = 1 ∧ (pPowersLT 2 (2 ^ 2 + 1)).length = 2 ∧
    (pPowersLT 3 (3 ^ 2)).length = 1 ∧ (pPowersLT 3 (3 ^ 2 + 1)).length = 2 ∧
    (pPowersLT 5 (5 ^ 2)).length = 1 ∧ (pPowersLT 5 (5 ^ 2 + 1)).length = 2 ∧
    (pPowersLT 7 (7 ^ 2)).length = 1 ∧ (pPowersLT 7 (7 ^ 2 + 1)).length = 2 := by decide

/-! ## The non-claim, as a theorem

The `p`-ladder is not the window. At `L = 4` the `2`-ladder carries one rung while the
full window carries two prime powers, because `3` is in the window and is not a power of
`2`. Stated here so the apex statement is never read as a statement about the window. -/

theorem apex_ladder_is_not_window :
    pPowersLT 2 4 = [2] ∧ primePowersLT 4 = [2, 3] ∧ pPowersLT 2 4 ≠ primePowersLT 4 := by
  decide

/-- And the same at the next two squares: the window at `p²` holds many prime powers the
`p`-ladder does not see. The coincidence is a statement about ONE prime's ladder. -/
theorem apex_window_is_larger :
    (pPowersLT 3 9).length = 1 ∧ (primePowersLT 9).length = 6 ∧
    (pPowersLT 5 25).length = 1 ∧ (primePowersLT 25).length = 13 := by decide

end SIDEWindow
