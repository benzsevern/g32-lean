import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalProductLocalCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleContractibleFactorProjection

/-! # Actual local support cap into intrinsic tangential point homology
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual local cap with a fixed ambient point class, followed by the literal projection to tangential point homology.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, local supported cap and relative homotopy invariance.
HC no distance; AV milestone no distance. -/
def properCycle_normal_product_support_cap
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) [T1Space Y] (y : Y) (p : ℕ)
    (c : orientationGroup (TopCat.of (E × Y)) (p + Module.finrank ℝ E) (0, y)) :
    CohomologyWithSupport ℚ (TopCat.of (E × Y)) (Prod.snd ⁻¹' ({y} : Set Y)) p →ₗ[ℚ]
      orientationGroup (TopCat.of E) (Module.finrank ℝ E) 0 :=
  (relativeHomologyMap ℚ (Module.finrank ℝ E)
    (properCycle_factor_projection_pair (TopCat.of E) Y ({0} : Set E)ᶜ)).comp
      ((triadCapCohomologyLinear ℚ (TopCat.of (E × Y))
        (Prod.snd ⁻¹' ({y} : Set Y)ᶜ) {w | w.1 = 0}ᶜ p (Module.finrank ℝ E)).flip
        ((properCycle_normal_product_triad_point_iso E Y y (p + Module.finrank ℝ E)).inv c))

/-- The original local support cap identifies supported cohomology with intrinsic tangential point homology for a contractible normal fibre and an actual ambient orientation generator.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, local cap duality in product models.
HC no distance; AV milestone no distance. -/
lemma properCycle_normal_product_support_cap_bijective
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) [T1Space Y] [ContractibleSpace Y] (y : Y) (p : ℕ) (hp : Even p)
    (c : orientationGroup (TopCat.of (E × Y)) (p + Module.finrank ℝ E) (0, y))
    (hc : Function.Bijective (LinearMap.toSpanSingleton ℚ _ c)) :
    Function.Bijective (properCycle_normal_product_support_cap E Y y p c) := by
  exact (properCycle_contractible_factor_projection_bijective (TopCat.of E) Y
    ({0} : Set E)ᶜ (Module.finrank ℝ E)).comp
      (properCycle_normal_product_point_cap_bijective E Y y p hp c hc)

end HodgeLean.Foundations.QuotientDuality
