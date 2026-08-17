/-
  SIDE-window · Sawtooth.lean
  ===========================

  THE INERTIA COUNT OF THE DISCRETE LAG FORM — its COMBINATORIAL half, compiled.

  Vanilla Lean 4. No Mathlib, no Batteries, no dependencies. Every theorem is closed by
  `decide`, so the whole file is checkable by the Lean kernel alone.

  ── THE STATEMENT THIS FILE IS THE ARITHMETIC HALF OF ───────────────────────────

  Let `S_k` be the `M × M` symmetric matrix with `(S_k)_{ij} = 1` exactly when `|i − j| = k`
  (the shifted-correlation form at shift `k` on `M` grid points). Then:

    (a) `i` and `j` are related only when `i = j ± k`, so `{0,…,M−1}` splits into the `k`
        residue classes modulo `k`, and `S_k` acts on each class as the adjacency matrix
        of a PATH GRAPH on its members.                     ← COMBINATORIAL, COMPILED HERE

    (b) the adjacency matrix of the path `P_m` has spectrum `2cos(πj/(m+1))`, `j = 1..m`,
        which is SYMMETRIC about `0` and has nullity `1` iff `m` is ODD.
                                                            ← SPECTRAL, **NOT COMPILED**

    (c) hence  #negatives = #positives = (M − nullity)/2,  nullity = #odd-length chains.
                                                            ← follows from (a) and (b)

  ### WHAT IS COMPILED BELOW IS (a), THE NULLITY COUNT, AND THE ARITHMETIC OF (c).
  ### WHAT IS NOT COMPILED IS (b), AND WITHOUT (b) NOTHING HERE IS A SPECTRAL STATEMENT.

  ── WHY (b) IS NOT HERE, RECORDED RATHER THAN GLOSSED ───────────────────────────

  (b) is a statement about eigenvalues of a real symmetric matrix. Stating it needs linear
  algebra over `ℝ` — spectra, multiplicity, symmetry of a spectrum — none of which exists in
  Lean 4 core. It would need Mathlib.

  ### MATHLIB IS NOT BUILT IN THIS ENVIRONMENT: `Mathlib.olean` is absent, and the local
  ### checkout's toolchain is `v4.30.0-rc1` against this repository's `v4.29.1`.
  Building it is not a half-sitting, and inventing a proof of (b) here would be worse than
  leaving it visibly undone. **It is left visibly undone.** If it is ever compiled it goes in
  a COMPANION module with its own axiom profile, so that this library's headline — *no
  axioms at all* — stays true of what is actually here.

  ── AND THE OPERATOR IS NOT THE FORM ────────────────────────────────────────────

  The bench measures `A = A_main + c·(ω/2)·S_k` restricted to a codimension-one subspace,
  not `S_k`. Its counts agree with `(M − nullity)/2` **to within one offender** across every
  window measured. ### THAT AGREEMENT IS BENCH-GRADE AND IS NOT PROVED ANYWHERE, HERE OR
  ### ELSEWHERE. `A_main` is measured to have 2–3 positive eigenvalues, so it is not
  negative semidefinite and no comparison theorem applies to it. Nothing in this file is
  evidence about the operator.

  ── AND THE USUAL NON-CLAIMS, REPEATED SO THEY TRAVEL ───────────────────────────

  * IT PROVES NOTHING ABOUT ζ, ABOUT `h2`, OR ABOUT ANY OPERATOR INEQUALITY. Nothing here
    bears on the sign of `W_∞ − W_2`.
  * IT PROVES NOTHING ABOUT REAL WINDOW LENGTHS. `M` and `k` are grid counts. The passage
    from a real window `log L` and a real lag `log 2` to the integers `M = round(log L/ω)`
    and `k = round(log 2/ω)` IS THE DISCRETIZATION ITSELF and is not formalized.
  * THE GENERAL `M`, `k` IS NOT PROVED. Every theorem below is `decide` on concrete values.
    The closed forms are STATED as definitions and CHECKED against the direct definitions on
    a family of small cases; they are not proved equal in general, because that needs
    induction and `decide` cannot give it.
-/

import SIDEWindow.Window

namespace SIDEWindow

/-! ## (a) The decomposition into residue chains

`chainLen M k r` counts the members of `{0,…,M−1}` congruent to `r` mod `k` — the length of
the `r`-th path in the decomposition. -/

def chainLen (M k r : Nat) : Nat := ((List.range M).filter (fun i => i % k == r)).length

/-- The chain lengths, one per residue `r < k`. -/
def chainLens (M k : Nat) : List Nat := (List.range k).map (chainLen M k)

/-- Sum of a list of naturals, so the partition check below is a statement and not a comment. -/
def sum : List Nat → Nat
  | [] => 0
  | a :: as => a + sum as

/-- ### THE DECOMPOSITION IS A PARTITION: the chain lengths sum to `M`. Checked, not assumed. -/
theorem chains_partition :
    sum (chainLens 7 5) = 7 ∧ sum (chainLens 12 5) = 12 ∧ sum (chainLens 17 5) = 17 ∧
    sum (chainLens 22 5) = 22 ∧ sum (chainLens 27 5) = 27 ∧ sum (chainLens 32 5) = 32 ∧
    sum (chainLens 37 5) = 37 ∧ sum (chainLens 30 7) = 30 ∧ sum (chainLens 31 4) = 31 := by
  decide

/-- The shape: with `M = q·k + s`, exactly `s` chains have length `q+1` and `k − s` have
length `q`. Here `M = 17 = 3·5 + 2`, so two chains of length `4` and three of length `3`. -/
theorem chain_shape :
    chainLens 17 5 = [4, 4, 3, 3, 3] ∧ chainLens 12 5 = [3, 3, 2, 2, 2] ∧
    chainLens 7 5 = [2, 2, 1, 1, 1] ∧ chainLens 30 7 = [5, 5, 4, 4, 4, 4, 4] := by decide

/-! ## The nullity, and the count

`nullity M k` is the number of ODD-length chains. Under the spectral input (b) — **which is
not compiled here** — this is the nullity of `S_k`, and the negative count is `(M − nullity)/2`. -/

def nullity (M k : Nat) : Nat := ((chainLens M k).filter (fun m => m % 2 == 1)).length

def negCount (M k : Nat) : Nat := (M - nullity M k) / 2

/-! ### Closed forms

`M = q·k + s` with `q = M / k` and `s = M % k`. The `s` long chains have length `q+1` and the
other `k − s` have length `q`, so the odd ones are the long ones when `q` is even and the
short ones when `q` is odd. -/

def nullityCF (M k : Nat) : Nat := if (M / k) % 2 == 0 then M % k else k - M % k

def negCountCF (M k : Nat) : Nat := (M - nullityCF M k) / 2

/-- ### THE CLOSED FORM AGREES WITH THE DIRECT DEFINITION on a family covering `q = 1 … 7`
and three different `k`. **This is a check on small cases, not a proof for general `M, k`.** -/
theorem nullity_cf_agrees :
    nullity 7 5 = nullityCF 7 5 ∧ nullity 12 5 = nullityCF 12 5 ∧
    nullity 17 5 = nullityCF 17 5 ∧ nullity 22 5 = nullityCF 22 5 ∧
    nullity 27 5 = nullityCF 27 5 ∧ nullity 32 5 = nullityCF 32 5 ∧
    nullity 37 5 = nullityCF 37 5 ∧ nullity 30 7 = nullityCF 30 7 ∧
    nullity 31 4 = nullityCF 31 4 ∧ nullity 41 6 = nullityCF 41 6 := by decide

/-- And so do the counts. -/
theorem negCount_cf_agrees :
    negCount 7 5 = negCountCF 7 5 ∧ negCount 12 5 = negCountCF 12 5 ∧
    negCount 17 5 = negCountCF 17 5 ∧ negCount 22 5 = negCountCF 22 5 ∧
    negCount 27 5 = negCountCF 27 5 ∧ negCount 32 5 = negCountCF 32 5 ∧
    negCount 37 5 = negCountCF 37 5 ∧ negCount 30 7 = negCountCF 30 7 := by decide

/-- ### `M` AND THE NULLITY HAVE THE SAME PARITY, so `(M − nullity)/2` is an exact halving
and not a truncation. *(The chain lengths sum to `M`, and a sum is odd exactly as often as
its odd summands are — checked here on the same family.)* -/
theorem count_is_exact_halving :
    (7 - nullity 7 5) % 2 = 0 ∧ (12 - nullity 12 5) % 2 = 0 ∧
    (17 - nullity 17 5) % 2 = 0 ∧ (22 - nullity 22 5) % 2 = 0 ∧
    (27 - nullity 27 5) % 2 = 0 ∧ (32 - nullity 32 5) % 2 = 0 ∧
    (37 - nullity 37 5) % 2 = 0 ∧ (30 - nullity 30 7) % 2 = 0 ∧
    2 * negCount 17 5 + nullity 17 5 = 17 ∧ 2 * negCount 30 7 + nullity 30 7 = 30 := by decide

/-! ## The sawtooth, as arithmetic

Writing `M = q·k + s`, the closed form evaluates to `M − m·k` when `q = 2m−1` and to `m·k`
when `q = 2m`. Odd `q` climbs, even `q` falls, and the two meet at exactly half. -/

/-- The teeth, on a clean grid (`k = 5`, `s = 0`) so the pattern is visible in the numbers:
`q = 1 → M − k`, `q = 2 → k`, `q = 3 → M − 2k`, `q = 4 → 2k`, `q = 5 → M − 3k`, `q = 6 → 3k`. -/
theorem the_teeth :
    negCountCF 5 5 = 0 ∧ negCountCF 10 5 = 5 ∧ negCountCF 15 5 = 5 ∧
    negCountCF 20 5 = 10 ∧ negCountCF 25 5 = 10 ∧ negCountCF 30 5 = 15 ∧
    negCountCF 35 5 = 15 := by decide

/-- ### AT EVERY EVEN `q` THE COUNT IS EXACTLY HALF THE GRID — the apex, `2·count = M`.
`q = 2, 4, 6, 8` at `k = 5`, and `q = 2, 4` at `k = 7` and `k = 11`. -/
theorem apex_is_exactly_half :
    2 * negCountCF 10 5 = 10 ∧ 2 * negCountCF 20 5 = 20 ∧ 2 * negCountCF 30 5 = 30 ∧
    2 * negCountCF 40 5 = 40 ∧ 2 * negCountCF 14 7 = 14 ∧ 2 * negCountCF 28 7 = 28 ∧
    2 * negCountCF 22 11 = 22 ∧ 2 * negCountCF 44 11 = 44 := by decide

/-- And at every ODD `q` it is strictly below half — the troughs. -/
theorem troughs_are_below_half :
    2 * negCountCF 15 5 < 15 ∧ 2 * negCountCF 25 5 < 25 ∧ 2 * negCountCF 35 5 < 35 ∧
    2 * negCountCF 21 7 < 21 ∧ 2 * negCountCF 33 11 < 33 := by decide

/-! ## The bench's own integers

The grids the corpus actually measured on, at `ω = 10⁻³` where `k = 693`, and at
`ω = 2×10⁻³` where `k = 347`. These are the integer predictions the bench was tested
against, certified here as arithmetic.

**They are predictions about `S_k` only.** The measured operator agreed with each of them to
within one offender; that agreement is bench-grade and is not compiled. -/

theorem bench_predictions_omega_1e3 :
    negCountCF 1163 693 = 470 ∧ negCountCF 1281 693 = 588 ∧ negCountCF 1435 693 = 693 ∧
    negCountCF 1526 693 = 693 ∧ negCountCF 1705 693 = 693 ∧ negCountCF 1946 693 = 693 ∧
    negCountCF 2079 693 = 693 ∧ negCountCF 2197 693 = 811 ∧ negCountCF 2485 693 = 1099 ∧
    negCountCF 2773 693 = 1386 ∧ negCountCF 2996 693 = 1386 ∧ negCountCF 3466 693 = 1387 ∧
    negCountCF 4159 693 = 2079 ∧ negCountCF 4852 693 = 2080 := by decide

theorem bench_predictions_omega_2e3 :
    negCountCF 582 347 = 235 ∧ negCountCF 718 347 = 347 ∧ negCountCF 973 347 = 347 ∧
    negCountCF 1040 347 = 347 ∧ negCountCF 1099 347 = 405 ∧ negCountCF 1242 347 = 548 ∧
    negCountCF 1386 347 = 692 ∧ negCountCF 1498 347 = 694 ∧ negCountCF 1733 347 = 694 ∧
    negCountCF 2079 347 = 1038 ∧ negCountCF 2426 347 = 1041 := by decide

/-- ### THE THIRD APEX, CERTIFIED AS AN INTEGER IDENTITY: at `ω = 10⁻³` and `L = 64` the grid
is `M = 4159` with `k = 693`, and the count is exactly half of `M − 1`. -/
theorem third_apex_at_L64 : 2 * negCountCF 4159 693 = 4158 ∧ negCountCF 4159 693 = 2079 := by
  decide

end SIDEWindow
