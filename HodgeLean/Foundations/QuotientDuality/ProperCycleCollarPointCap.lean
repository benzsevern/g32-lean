import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarPointPair
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeTriadCapCohomology
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodFundamental

/-! # Original support point values through the literal collar triad cap
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual local value of the constructed support cap is the original triad cap modulo the literal retraction fibre, evaluated on the original excised ambient class.
Source: ProperCycleSupportCollar.cap_point_projection; properCycle_relative_triad_cap_cohomology.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.cap_point_triad {X : TopCat.{0}} {S : Set X}
    (C : ProperCycleSupportCollar X S) (hS : IsClosed S) (z : S) (p q : ℕ)
    (a : CohomologyWithSupport ℚ X S p) (c : Homology ℚ X (p+q)) :
    let U := TopCat.of C.neighborhood
    let A : Set U := Subtype.val ⁻¹' Sᶜ
    let B : Set U := C.retraction ⁻¹' ({z} : Set S)ᶜ
    localOrientation (TopCat.of S) q (C.cap hS p q c a) z =
      relativeHomologyMap ℚ q (C.pointPairMap z)
        (triadCapCohomologyLinear ℚ U A B p q
          (relativeCohomologyMap ℚ p (b6m_subspacePairMap X C.neighborhood Sᶜ) a)
          ((HomologicalComplex.homologyMap (properCycle_relative_to_triad_chain_map U A B)
            (p+q)).hom
            (properCycle_neighborhood_relative_fundamental X S C.neighborhood hS C.isOpen
              C.contains (p+q) c))) := by
  dsimp only
  rw [C.cap_point_projection hS z p q a c]
  apply congrArg (relativeHomologyMap ℚ q (C.pointPairMap z))
  exact properCycle_relative_triad_cap_cohomology (TopCat.of C.neighborhood)
    (Subtype.val ⁻¹' Sᶜ) (C.retraction ⁻¹' ({z} : Set S)ᶜ) p q
    (relativeCohomologyMap ℚ p (b6m_subspacePairMap X C.neighborhood Sᶜ) a)
    (properCycle_neighborhood_relative_fundamental X S C.neighborhood hS C.isOpen
      C.contains (p+q) c)

end HodgeLean.Foundations.QuotientDuality
