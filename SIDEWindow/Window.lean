/-
  SIDE-window · Window.lean
  =========================

  LEMMA A AND THE WINDOW ARITHMETIC, as decidable statements about small naturals.

  Vanilla Lean 4. No Mathlib, no Batteries, no dependencies. Every theorem below is
  closed by `decide`, so the whole file is checkable by the Lean kernel alone.

  ── WHAT THIS KERNEL DOES NOT CLAIM ─────────────────────────────────────────────

  Read this before citing anything here.

  * IT PROVES NOTHING ABOUT ζ, ABOUT `h2`, OR ABOUT ANY OPERATOR INEQUALITY.
    It is elementary counting of prime powers below small bounds. Nothing in this
    file bears on the sign of `W_∞ − W_2`, and no result here may be cited as
    evidence about it.

  * IT PROVES NOTHING ABOUT REAL INTERVALS. The corpus states Lemma A as
    "for λ² ∈ (2,3) the prime side has exactly one term, p^k = 2". That sentence
    quantifies over a real interval. THIS FILE PROVES THE ARITHMETIC RESIDUE ONLY:
    the prime powers `n ≤ 2` are exactly `[2]`. The step from "λ² ∈ (2,3)" to
    "n ≤ 2" is the observation that a prime power is a natural number and a natural
    number `< 3` is `≤ 2`. That step is ONE LINE OF ORDINARY MATHEMATICS AND IT IS
    NOT FORMALIZED HERE. A reader who wants Lemma A as stated in the corpus must
    supply it.

  * THE "WINDOWS" ARE HALF-VACUOUS, AND SAYING SO IS PART OF THE RESULT.
    The corpus writes the windows multiplicatively as `(1/2, 2)` and `(1/3, 3)`.
    Every prime power is `≥ 2 > 1 ≥ 1/L`, so THE LOWER ENDPOINT NEVER BINDS: the
    entire content of both window statements lives in the upper bound. The theorems
    below are therefore stated as counts below an integer bound, which is what they
    actually are.

  * MAXIMALITY OVER REAL `L` IS NOT PROVED. `window_two_is_maximal_prime_free` and
    `window_three_is_maximal_one_prime` establish maximality AT INTEGER BOUNDS ONLY.
    Extending to real `L` uses the fact that `L ↦ #{prime powers < L}` is a step
    function whose jumps occur exactly at prime powers, so it is constant between
    consecutive ones. That argument is standard and IS NOT IN THIS FILE.

  * `IsPrime` HERE IS TRIAL DIVISION, NOT AN IMPORTED NOTION. It is defined below
    and agrees with the usual definition on the naturals; it is not `Nat.Prime`
    from Mathlib, and no lemma about it is imported or assumed.

  ── THE δ/L LAW IS NOT IN THIS KERNEL ───────────────────────────────────────────

  The corpus's `δ/L` law — Φ's negative fraction `= 1 − log 2 / log L`, measured at
  bank over `L ∈ {2.2, 2.5, 3.0, 3.5, 4.0}` with residuals of order `1/dim` — is a
  CONJECTURE WITH A MEASURED TABLE. It is MEASURED-AT-BANK, never proved, and its
  two largest rows (`L = 3.5`, `L = 4.0`) extrapolate past the `(1,3]` range that
  Lemma 5.2's un-run re-derivation would cover.

  IT APPEARS IN THIS KERNEL ONLY AS THIS COMMENT. There is deliberately no
  definition, no statement and no theorem about it below, because a Lean file
  containing a name for it would invite a citation it cannot support.
-/

namespace SIDEWindow

/-! ## Primality, by trial division

`IsPrime n` is `2 ≤ n` together with: no `d` in the range `2 ≤ d < n` divides `n`. -/

def IsPrime (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range n).all (fun d => decide (d < 2) || decide (n % d ≠ 0))

/-- Sanity, so the definition is pinned by examples and not only by its text. -/
theorem isPrime_examples :
    IsPrime 0 = false ∧ IsPrime 1 = false ∧ IsPrime 2 = true ∧
    IsPrime 3 = true ∧ IsPrime 4 = false ∧ IsPrime 9 = false := by decide

/-! ## Prime powers

`IsPrimePower n` holds when `n = p ^ k` for some prime `p` and some `k ≥ 1`.

The search bounds `p ≤ n` and `k ≤ n` lose nothing: a prime `p ≥ 2` with `p ^ k = n`
and `k ≥ 1` forces both `p ≤ n` and `k ≤ n`. -/

def IsPrimePower (n : Nat) : Bool :=
  (List.range (n + 1)).any fun p =>
    IsPrime p && (List.range (n + 1)).any fun k => decide (1 ≤ k) && decide (p ^ k = n)

theorem isPrimePower_examples :
    IsPrimePower 0 = false ∧ IsPrimePower 1 = false ∧ IsPrimePower 2 = true ∧
    IsPrimePower 3 = true ∧ IsPrimePower 4 = true ∧ IsPrimePower 6 = false ∧
    IsPrimePower 8 = true ∧ IsPrimePower 9 = true := by decide

/-- The prime powers `≤ x`, in increasing order. -/
def primePowersLE (x : Nat) : List Nat := (List.range (x + 1)).filter IsPrimePower

/-- The prime powers `< x`, in increasing order. -/
def primePowersLT (x : Nat) : List Nat := (List.range x).filter IsPrimePower

/-! ## Lemma A

The arithmetic residue of "for `λ² ∈ (2,3)` the prime side has exactly one term,
namely `p^k = 2`": the prime powers not exceeding `2` are exactly `[2]`.

As recorded in the header, the reduction from the real interval `(2,3)` to the
bound `2` is not formalized here. -/

theorem lemmaA : primePowersLE 2 = [2] := by decide

/-- Lemma A restated as a count: exactly one prime power is `≤ 2`. -/
theorem lemmaA_count : (primePowersLE 2).length = 1 := by decide

/-! ## The window arithmetic

Windows are written `(1/L, L)` in the corpus. The lower endpoint never binds
(every prime power is `≥ 2`), so each statement is a count below `L`. -/

/-- The window `(1/2, 2)` is prime-free: no prime power lies below `2`. -/
theorem window_prime_free : primePowersLT 2 = [] := by decide

/-- The window `(1/3, 3)` carries exactly one prime power, namely `2`. -/
theorem window_one_prime : primePowersLT 3 = [2] := by decide

/-- At the next integer bound the count is already two. -/
theorem window_four_has_two : primePowersLT 4 = [2, 3] := by decide

/-- `2` is the largest INTEGER bound giving a prime-free window: nothing lies below
`2`, and something does lie below `3`. Maximality over real `L` is not proved here. -/
theorem window_two_is_maximal_prime_free :
    primePowersLT 2 = [] ∧ primePowersLT 3 ≠ [] := by decide

/-- `3` is the largest INTEGER bound giving a one-prime window: the count below `3`
is `1`, and the count below `4` is `2`. Maximality over real `L` is not proved here. -/
theorem window_three_is_maximal_one_prime :
    (primePowersLT 3).length = 1 ∧ (primePowersLT 4).length = 2 := by decide

/-- The counting function on the range this kernel speaks about, tabulated. -/
theorem primePower_counts :
    (primePowersLT 2).length = 0 ∧ (primePowersLT 3).length = 1 ∧
    (primePowersLT 4).length = 2 ∧ (primePowersLT 5).length = 3 ∧
    (primePowersLT 9).length = 6 ∧ (primePowersLT 10).length = 7 := by decide

/-- The tabulated range, listed rather than counted, so the counts above are
readable against the members that produce them. `6` is absent (it is `2 · 3`). -/
theorem primePowers_below_ten : primePowersLT 10 = [2, 3, 4, 5, 7, 8, 9] := by decide

end SIDEWindow
