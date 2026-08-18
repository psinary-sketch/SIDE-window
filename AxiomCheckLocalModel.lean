/-
  SIDE-window · AxiomCheckLocalModel.lean
  =======================================

  Axiom profile for every terminal in `SIDEWindow/LocalModel.lean`.

  Run:  lake env lean AxiomCheckLocalModel.lean

  Expected, for every line: "does not depend on any axioms".

  NOTE ON WHAT THIS PROFILE DOES AND DOES NOT CERTIFY. Every theorem below is a COUNTING
  or ARITHMETIC statement about the finite model `ℤ/p^{2n}` at fixed cells — fixed-point
  counts, absorption counts, ball closure, the orbit census, and the laws' integer
  identities. The LINEAR-ALGEBRAIC and ANALYTIC inputs (that these counts are dimensions
  and traces of the bench's operators; the forest-components lemma) are NOT in this
  repository — they are bench-certified at `relay` with their registrations. An axiom-free
  profile here certifies the arithmetic and says nothing beyond it. NOTHING HERE BEARS ON h2.
-/
import SIDEWindow.LocalModel

open SIDEWindow.LocalModel

#print axioms fixed_2_1
#print axioms fixed_2_2
#print axioms fixed_2_3
#print axioms fixed_2_4
#print axioms fixed_3_1
#print axioms fixed_3_2
#print axioms fixed_5_1
#print axioms absorb_2_2
#print axioms absorb_2_3
#print axioms absorb_2_4
#print axioms absorb_3_2
#print axioms absorb_5_1
#print axioms closed_2_2
#print axioms closed_2_3
#print axioms closed_2_4
#print axioms closed_3_2
#print axioms closed_5_1
#print axioms census_2_2
#print axioms census_2_3
#print axioms census_2_4
#print axioms census_3_2
#print axioms census_5_1
#print axioms soninSplit
#print axioms orbitCount
#print axioms diagLaw
#print axioms fifthLaw
