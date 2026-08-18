/-
  SIDE-window · LocalModel.lean
  =============================

  THE LOCAL MODEL'S CENSUS — the counting laws of the finite p-adic model, compiled.

  Vanilla Lean 4. No Mathlib, no Batteries, no dependencies. Every theorem is closed by
  `decide`, so the whole file is checkable by the Lean kernel alone.

  ── THE MODEL ───────────────────────────────────────────────────────────────────

  `G = p^{−n}ℤ_p / p^{n}ℤ_p ≅ ℤ/p^{2n}` via `x = p^{−n}·m`.  The INTEGERS' BALL is
  `B = {m : p^n ∣ m}` (the elements with `|x|_p ≤ 1`).  Scaling by `p` is `m ↦ p·m mod p^{2n}`.
  The decomposition the census makes explicit:  every `m` is `p^v·u` with `u` a unit —
  UNIT GROUP × valuation; the BALL is `v ≥ n`; the ORBITS of `m ∼ p·m` on the off-ball
  part are the classes the quotient trace lives on.

  ── WHAT IS COMPILED HERE, AND WHAT IS NOT ──────────────────────────────────────

  COMPILED (decide, at the fixed cells (p,n) listed below — "the stated range"):

    (F)  the FIXED-POINT COUNT:  #{m : p^k·m ≡ m mod p^{2n}} = 1  (only m = 0) — the
         arithmetic heart of the absorption proof's lemma (iii) and of the trace
         localization: gcd(p^k − 1, p^{2n}) = 1 isolates zero.
    (A)  the ABSORPTION COUNT:   #{m : m·(p^k − 1) ≡ 0 mod p^n} = p^n — lemma (iv).
    (C)  BALL CLOSURE:           p^n ∣ m  →  p^n ∣ (p·m mod p^{2n}) — lemma (v)'s ground.
    (O)  the OFF-BALL COUNT:     #off-ball = p^{2n} − p^n.
    (E)  the EDGE COUNT:         #{m off-ball : p·m off-ball} = p^{2n} − p^{n+1}.
    (V)  the CENSUS IDENTITIES, per cell:
           (p^n − 1)²  +  (2p^n − 1)  =  p^{2n}          (the Sonin-dimension split)
           (p^{2n} − p^n) − (p^{2n} − p^{n+1}) = (p−1)p^n (the orbit count, V − E)
           d_k-identity:  (p^{n−k} − 1)·(p^n − 1)          (the diagonal-law values)
           fifth-law numerator: (p−1)·p^{n+1}·(p^{n−1} − p^{k−1})  ≡ R(k)·(p^n − 1)/(p−1)…
           …compiled as the integer identity at each cell (see `fifthLaw_*` below).

  NOT COMPILED, DECLARED RATHER THAN GLOSSED:

    · That `(p^n − 1)²` is the DIMENSION of the Sonin kernel needs linear algebra over ℂ
      (rank of the constraint stack = 2p^n − 1): bench-certified, not compiled. What is
      compiled is the arithmetic split the rank statement asserts.
    · That orbit count = V − E needs the forest-components lemma (the relation m ∼ p·m is
      ACYCLIC off-ball — which follows from (F), since a cycle would be a fixed point of
      some p^k — and components of an acyclic functional graph number V − E): the graph
      lemma is standard and NOT compiled here; (F), (O), (E) compile its inputs.
    · That the d_k and fifth-law values are TRACES of the bench's operators is analytic,
      bench-grade, and says NOTHING about h2. The kernel compiles the census arithmetic;
      the analytic identification lives at `relay` with its registrations.

  NO SIGN. NOTHING HERE BEARS ON h2. The census is a statement about a finite model.
-/

namespace SIDEWindow.LocalModel

/- `maxRecDepth` is an ELABORATION limit (the `N = 256` cells overrun the default while
   building their `List.range`); raising it adds no axiom and changes no proof content. -/
set_option maxRecDepth 8192

/-- the model size `p^{2n}` -/
def modN (p n : Nat) : Nat := p ^ (2 * n)

/-- ball membership: `p^n ∣ m` -/
def inBall (p n m : Nat) : Bool := m % p ^ n == 0

/-- (F) the fixed-point count of `m ↦ p^k·m` on `ℤ/p^{2n}` -/
def fixedCount (p n k : Nat) : Nat :=
  ((List.range (modN p n)).filter (fun m => (p ^ k * m) % modN p n == m)).length

/-- (A) the absorption count: solutions of `m·(p^k − 1) ≡ 0 mod p^n` in `ℤ/p^{2n}` -/
def absorbCount (p n k : Nat) : Nat :=
  ((List.range (modN p n)).filter (fun m => (m * (p ^ k - 1)) % p ^ n == 0)).length

/-- (C) ball closure under scaling, checked over the whole cell -/
def ballClosed (p n : Nat) : Bool :=
  (List.range (modN p n)).all (fun m => !inBall p n m || inBall p n ((p * m) % modN p n))

/-- (O) the off-ball count -/
def offBallCount (p n : Nat) : Nat :=
  ((List.range (modN p n)).filter (fun m => !inBall p n m)).length

/-- (E) the edge count of the orbit relation on the off-ball part -/
def edgeCount (p n : Nat) : Nat :=
  ((List.range (modN p n)).filter
    (fun m => !inBall p n m && !inBall p n ((p * m) % modN p n))).length

/- ── (F) THE FIXED-POINT COUNT = 1, per cell and lag ───────────────────────── -/

theorem fixed_2_1 : fixedCount 2 1 1 = 1 := by decide
theorem fixed_2_2 : (fixedCount 2 2 1 = 1) ∧ (fixedCount 2 2 2 = 1) ∧ (fixedCount 2 2 3 = 1) := by decide
theorem fixed_2_3 : (fixedCount 2 3 1 = 1) ∧ (fixedCount 2 3 2 = 1) ∧ (fixedCount 2 3 3 = 1)
    ∧ (fixedCount 2 3 4 = 1) ∧ (fixedCount 2 3 5 = 1) := by decide
theorem fixed_2_4 : (fixedCount 2 4 1 = 1) ∧ (fixedCount 2 4 2 = 1) ∧ (fixedCount 2 4 3 = 1) := by decide
theorem fixed_3_1 : fixedCount 3 1 1 = 1 := by decide
theorem fixed_3_2 : (fixedCount 3 2 1 = 1) ∧ (fixedCount 3 2 2 = 1) ∧ (fixedCount 3 2 3 = 1) := by decide
theorem fixed_5_1 : fixedCount 5 1 1 = 1 := by decide

/- ── (A) THE ABSORPTION COUNT = p^n, per cell and lag ──────────────────────── -/

theorem absorb_2_2 : (absorbCount 2 2 1 = 4) ∧ (absorbCount 2 2 2 = 4) ∧ (absorbCount 2 2 3 = 4) := by decide
theorem absorb_2_3 : (absorbCount 2 3 1 = 8) ∧ (absorbCount 2 3 2 = 8) ∧ (absorbCount 2 3 3 = 8) := by decide
theorem absorb_2_4 : (absorbCount 2 4 1 = 16) ∧ (absorbCount 2 4 2 = 16) := by decide
theorem absorb_3_2 : (absorbCount 3 2 1 = 9) ∧ (absorbCount 3 2 2 = 9) := by decide
theorem absorb_5_1 : absorbCount 5 1 1 = 5 := by decide

/- ── (C) BALL CLOSURE, per cell ────────────────────────────────────────────── -/

theorem closed_2_2 : ballClosed 2 2 = true := by decide
theorem closed_2_3 : ballClosed 2 3 = true := by decide
theorem closed_2_4 : ballClosed 2 4 = true := by decide
theorem closed_3_2 : ballClosed 3 2 = true := by decide
theorem closed_5_1 : ballClosed 5 1 = true := by decide

/- ── (O)/(E) THE ORBIT CENSUS: off-ball and edge counts, per cell ──────────── -/

theorem census_2_2 : (offBallCount 2 2 = 12) ∧ (edgeCount 2 2 = 8) := by decide
theorem census_2_3 : (offBallCount 2 3 = 56) ∧ (edgeCount 2 3 = 48) := by decide
theorem census_2_4 : (offBallCount 2 4 = 240) ∧ (edgeCount 2 4 = 224) := by decide
theorem census_3_2 : (offBallCount 3 2 = 72) ∧ (edgeCount 3 2 = 54) := by decide
theorem census_5_1 : (offBallCount 5 1 = 20) ∧ (edgeCount 5 1 = 0) := by decide

/- ── (V) THE CENSUS IDENTITIES — the four laws' arithmetic, per cell ───────── -/

/-- the Sonin-dimension split `(p^n−1)² + (2p^n−1) = p^{2n}` at the stated cells -/
theorem soninSplit :
    (3^2 + 7 = 16) ∧ (7^2 + 15 = 64) ∧ (15^2 + 31 = 256)
    ∧ (8^2 + 17 = 81) ∧ (4^2 + 9 = 25) ∧ (24^2 + 49 = 625) := by decide

/-- the orbit count `V − E = (p−1)p^n` at the stated cells (the graph lemma NOT compiled) -/
theorem orbitCount :
    (12 - 8 = 4) ∧ (56 - 48 = 8) ∧ (240 - 224 = 16) ∧ (72 - 54 = 18) ∧ (20 - 0 = 20) := by decide

/-- the diagonal law's values `d_k = (p^{n−k}−1)(p^n−1)` at the measured cells -/
theorem diagLaw :
    ((2^1 - 1) * (2^2 - 1) = 3) ∧ ((2^2 - 1) * (2^3 - 1) = 21) ∧ ((2^1 - 1) * (2^3 - 1) = 7)
    ∧ ((3^1 - 1) * (3^2 - 1) = 16) ∧ ((3^2 - 1) * (3^3 - 1) = 208) ∧ ((3^1 - 1) * (3^3 - 1) = 52)
    ∧ ((5^1 - 1) * (5^2 - 1) = 96) := by decide

/-- the fifth law `R(k) = (p−1)·p^{n+1}·(p^{n−1}−p^{k−1})/(p^n−1)`, compiled in the
    cross-multiplied integer form `R_num·(p^n−1) = R_den·(p−1)·p^{n+1}·(p^{n−1}−p^{k−1})`
    at the banked cells (the rationals `R_num/R_den` are `relay`'s exact bench values) -/
theorem fifthLaw :
    (8 * 3 = 3 * (1 * 8 * (2 - 1)))               -- (p,n,k)=(2,2,1): R = 8/3
    ∧ (48 * 7 = 7 * (1 * 16 * (4 - 1)))           -- (2,3,1): R = 48/7
    ∧ (32 * 7 = 7 * (1 * 16 * (4 - 2)))           -- (2,3,2): R = 32/7
    ∧ (648 * 26 = 13 * (2 * 81 * (9 - 1)))        -- (3,3,1): R = 648/13
    ∧ (486 * 26 = 13 * (2 * 81 * (9 - 3)))        -- (3,3,2): R = 486/13
    ∧ (250 * 24 = 3 * (4 * 125 * (5 - 1)))        -- (5,2,1): R = 250/3
    ∧ (1029 * 48 = 4 * (6 * 343 * (7 - 1)))       -- (7,2,1): R = 1029/4
    := by decide

end SIDEWindow.LocalModel
