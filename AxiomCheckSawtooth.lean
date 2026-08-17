/-
  SIDE-window · AxiomCheckSawtooth.lean
  =====================================

  Axiom profile for every terminal in `SIDEWindow/Sawtooth.lean`.

  Run:  lake env lean AxiomCheckSawtooth.lean

  Expected, for every line: "does not depend on any axioms".

  NOTE ON WHAT THIS PROFILE DOES AND DOES NOT CERTIFY. Every theorem below is a
  COMBINATORIAL statement — chain lengths, an odd-length count, and arithmetic on the
  resulting integers. The SPECTRAL input that turns them into a statement about negative
  eigenvalues (the path graph's spectrum is symmetric with nullity 1 iff its length is odd)
  is NOT in this repository. An axiom-free profile here certifies the arithmetic and says
  nothing about the spectral half.
-/

import SIDEWindow.Sawtooth

#print axioms SIDEWindow.chains_partition
#print axioms SIDEWindow.chain_shape
#print axioms SIDEWindow.nullity_cf_agrees
#print axioms SIDEWindow.negCount_cf_agrees
#print axioms SIDEWindow.count_is_exact_halving
#print axioms SIDEWindow.the_teeth
#print axioms SIDEWindow.apex_is_exactly_half
#print axioms SIDEWindow.troughs_are_below_half
#print axioms SIDEWindow.bench_predictions_omega_1e3
#print axioms SIDEWindow.bench_predictions_omega_2e3
#print axioms SIDEWindow.third_apex_at_L64
