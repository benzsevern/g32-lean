import HodgeLean.Papers.G32Family
import HodgeLean.Papers.PapersG32Certificates

/-! # G32 cycle-supplier definitions

The direct Proposition 4.6 premise for stage 3 of the G32 route. HC no distance; AV milestone
no distance.
-/

noncomputable section

open HodgeLean.RealDefs

namespace HodgeLean.Papers

/-- Proposition 4.6's cycle-supplier output for every fibre.
Source: G32 v0.16, Proposition 4.6, using Proposition 4.5;
Schoen, Theorem 2.0 and Corollary 3.1; Milne, Theorem 3.2. -/
def g32s_Prop46 (P : g32h_PrymFamily) : Prop :=
  ∀ s, g32t_WeilAlg (P.fiber s)

example {P : g32h_PrymFamily} (h46 : g32s_Prop46 P) (s : P.S) :
    g32t_WeilAlg (P.fiber s) :=
  h46 s

end HodgeLean.Papers
