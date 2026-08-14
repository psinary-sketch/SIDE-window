/-
  SIDE-window · Ladder.lean
  =========================

  THE WINDOW LADDER: the two-prime window, and the per-rung prime-power count.

  Vanilla Lean 4. No Mathlib, no Batteries, no dependencies. Every theorem is closed by
  `decide`, so the whole file is checkable by the Lean kernel alone.

  This extends `Window.lean` one rung: `Window.lean` proves the prime-free window
  `(1/2, 2)` and the one-prime window `(1/3, 3)`; this file proves the **two-prime**
  window `(1/4, 4)` and tabulates the counting function `W` that generates all of them.

  ── WHAT THIS FILE DOES NOT CLAIM ───────────────────────────────────────────────

  Every non-claim carried by `Window.lean` applies here unchanged, and is repeated
  rather than cross-referenced, because a reader may open this file first:

  * IT PROVES NOTHING ABOUT ζ, ABOUT `h2`, OR ABOUT ANY OPERATOR INEQUALITY.
    Nothing here bears on the sign of `W_∞ − W_2`, and no result may be cited as
    evidence about it. The letter `W` below is a COUNTING FUNCTION on naturals and has
    NO RELATION WHATEVER to the corpus's `W_2` / `W_∞`. The collision of names is
    unfortunate and is flagged here so it cannot mislead: `W n` counts prime powers
    below `n`, nothing else.

  * IT PROVES NOTHING ABOUT REAL INTERVALS. The windows are written `(1/L, L)` in the
    corpus. Every prime power is `≥ 2 > 1 ≥ 1/L`, so THE LOWER ENDPOINT NEVER BINDS and
    each statement is a count below an upper bound, which is what it is.

  * MAXIMALITY IS AT INTEGER BOUNDS ONLY. `window_four_is_maximal_two_prime` says the
    count below `4` is `2` and the count below `5` is `3`. Extending to real `L` uses
    that `L ↦ W L` is a step function jumping exactly at prime powers, hence constant
    between consecutive ones. THAT ARGUMENT IS STANDARD AND IS NOT IN THIS FILE.

  * `W` IS TABULATED, NOT CHARACTERIZED. The theorems below give `W` at named points.
    No closed form, no asymptotic, and no growth statement is proved or implied. In
    particular nothing here is a Chebyshev or prime-counting estimate.

  ── THE δ/L LAW IS NOT IN THIS KERNEL ───────────────────────────────────────────

  As in `Window.lean`: the `δ/L` law is a CONJECTURE WITH A MEASURED TABLE,
  `MEASURED-AT-BANK` and never proved. It appears in this repository only as a comment.
  There is deliberately no definition, statement or theorem about it.
-/

import SIDEWindow.Window

namespace SIDEWindow

/-! ## The counting function

`W n` is the number of prime powers strictly below `n`. It is the function that
generates every window statement in this repository: a window `(1/L, L)` carries
`W L` prime powers. -/

/-- The number of prime powers `< n`. **Not** the corpus's `W_2` / `W_∞`; see the
header. -/
def W (n : Nat) : Nat := (primePowersLT n).length

/-! ## The two-prime window -/

/-- The window `(1/4, 4)` carries exactly two prime powers, `2` and `3`. -/
theorem window_two_prime : primePowersLT 4 = [2, 3] := by decide

/-- Its count, stated separately so a citer can use the number without the list. -/
theorem window_two_prime_count : W 4 = 2 := by decide

/-- `4` is the largest INTEGER bound giving a two-prime window: the count below `4` is
`2`, and the count below `5` is `3`. Maximality over real `L` is not proved here. -/
theorem window_four_is_maximal_two_prime : W 4 = 2 ∧ W 5 = 3 := by decide

/-- The three windows of this repository in one statement: prime-free at `2`,
one-prime at `3`, two-prime at `4` — and the count is strictly increasing across
them, so each is the largest of its kind at integer bounds. -/
theorem the_window_ladder :
    W 2 = 0 ∧ W 3 = 1 ∧ W 4 = 2 ∧ W 5 = 3 := by decide

/-! ## The per-rung count

`W` tabulated on the first rungs. `W` is constant between consecutive prime powers and
steps by one at each — visible directly in the table below, and *not* proved as a
general statement. -/

theorem W_table_low :
    W 2 = 0 ∧ W 3 = 1 ∧ W 4 = 2 ∧ W 5 = 3 ∧ W 6 = 4 ∧
    W 7 = 4 ∧ W 8 = 5 ∧ W 9 = 6 ∧ W 10 = 7 := by decide

theorem W_table_mid :
    W 11 = 7 ∧ W 12 = 8 ∧ W 13 = 8 ∧ W 14 = 9 ∧ W 15 = 9 ∧
    W 16 = 9 ∧ W 17 = 10 ∧ W 18 = 11 := by decide

/-- The one flat step in the low table, isolated: `W 6 = W 7` because `6 = 2 · 3` is
not a prime power. The first composite that is not a prime power is where the counting
function first fails to advance. -/
theorem W_flat_at_six : W 6 = W 7 := by decide

/-- Likewise `W 14 = W 15 = W 16` — `14 = 2·7` and `15 = 3·5` are not prime powers,
so the count is flat across two consecutive rungs for the first time. -/
theorem W_flat_run_at_fourteen : W 14 = W 15 ∧ W 15 = W 16 := by decide

/-- The prime powers below `18`, listed, so every count above is readable against the
members that produce it. `6`, `10`, `12`, `14`, `15` are absent, being composite and
not prime powers. -/
theorem primePowers_below_eighteen :
    primePowersLT 18 = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17] := by decide

end SIDEWindow
