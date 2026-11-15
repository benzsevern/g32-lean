import HodgeLean.Adapters.CycleClassDivisorProductProofs

/-! # First supported-product layer: frozen specification

An implication from actual relative cochains: their ambient cup product annihilates
chains small in either complement. Excision, cohomology descent, comparison with
`cupProductOf`, local normalization and the divisor comparison remain open.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Adapters

/-- The ambient relative cup lift vanishes on chains small in either complement.
No openness is needed for this cochain statement; excision will need open complements.
Source: Hatcher, Algebraic Topology, §3.2, relative cup product construction;
Spanier, Algebraic Topology, chapters 5–6, small chains and products. -/
theorem ccm13_relativeCupLift_small_zero (Y : TopCat.{0})
    (S T : Set Y) (p q : ℕ)
    (u : RelativeCochain ℚ (TopPair.ofSubset Sᶜ) p)
    (v : RelativeCochain ℚ (TopPair.ofSubset Tᶜ) q) :
    smallCochainRestriction Y (ccm13_complementFamily Y S T) (p + q)
      (ccm13_relativeCupLift Y S T p q u v) = 0 :=
  ccm13_relativeCupLift_small_zero_aux Y S T p q u v

/-- Source: the zero relative cochains on the one-point space, in positive degrees. -/
example : smallCochainRestriction (TopCat.of PUnit)
    (ccm13_complementFamily (TopCat.of PUnit) ∅ Set.univ) (2 + 2)
    (ccm13_relativeCupLift (TopCat.of PUnit) ∅ Set.univ 2 2 0 0) = 0 :=
  ccm13_relativeCupLift_small_zero (TopCat.of PUnit) ∅ Set.univ 2 2 0 0

/-- Source: the constructed unit cochains for full support on a point. -/
example : smallCochainRestriction (TopCat.of PUnit)
    (ccm13_complementFamily (TopCat.of PUnit) Set.univ Set.univ) (0 + 0)
    (ccm13_relativeCupLift (TopCat.of PUnit) Set.univ Set.univ 0 0
      ccm13_pointUnit ccm13_pointUnit) = 0 :=
  ccm13_relativeCupLift_small_zero (TopCat.of PUnit) Set.univ Set.univ 0 0
    ccm13_pointUnit ccm13_pointUnit

end HodgeLean.Adapters
