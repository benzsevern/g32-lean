import HodgeLean.Papers.G32SupplyProofs

/-! # G32 Theorem A, stage 3: cycle suppliers (FROZEN SPEC)

This module records the fifty-one printed admissibility checks and the direct Proposition 4.6
premise for algebraicity of the Weil classes on every fibre of a `g32h_PrymFamily`.

Claimed: the printed table has fifty-one admissible rows. Proposition 4.6 enters as a direct
premise. The geometric use of the finite certificates is not checked here. Theorem A remains
unasserted. HC no distance; AV milestone no distance.
-/

namespace HodgeLean.Papers

/-- The printed supplier table contains fifty-one rows, each with positive even `h` and simple
branch exponents.
Source: G32 v0.16, Appendix B, Table 1 and Section 4.1. -/
theorem g32s_fifty_one_admissible :
    g32WitnessTable.length = 51 ∧
    (∀ r ∈ g32WitnessTable, 0 < r.h ∧ Even r.h ∧ IsSimpleExps r.m (expandExps r.exps)) :=
  g32s_fifty_one_admissible_aux

example : g32WitnessTable.length = 51 := g32s_fifty_one_admissible.1

/-- Proposition 4.6's cycle-supplier output for every fibre.
Source: G32 v0.16, Proposition 4.6, using Proposition 4.5;
Schoen, Theorem 2.0 and Corollary 3.1; Milne, Theorem 3.2. -/
theorem g32s_fiber_alg (P : g32h_PrymFamily) (h46 : g32s_Prop46 P) :
    ∀ s, g32t_WeilAlg (P.fiber s) :=
  h46

end HodgeLean.Papers
