/-
  SIDE-window · AxiomCheckApex.lean
  =================================

  Axiom profile for every terminal in `SIDEWindow/Apex.lean`.

  Run:  lake env lean AxiomCheckApex.lean

  Expected, for every line below: "does not depend on any axioms" — not the standard
  three, but NONE. Everything in `Apex.lean` is closed by `decide` or by core rewriting
  on `Nat`, so the kernel checks it outright.
-/

import SIDEWindow.Apex

#print axioms SIDEWindow.isPowerOf_examples
#print axioms SIDEWindow.turn_is_square
#print axioms SIDEWindow.apex_2
#print axioms SIDEWindow.apex_3
#print axioms SIDEWindow.apex_5
#print axioms SIDEWindow.apex_7
#print axioms SIDEWindow.apex_11
#print axioms SIDEWindow.apex_13
#print axioms SIDEWindow.apex_counts
#print axioms SIDEWindow.apex_is_the_entry_point
#print axioms SIDEWindow.apex_ladder_is_not_window
#print axioms SIDEWindow.apex_window_is_larger
