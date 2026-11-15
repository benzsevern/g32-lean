import HodgeLean.Foundations.QuotientDuality.ProperCycleBilinearOrientation
import HodgeLean.Foundations.QuotientDuality.ProperCycleOrientedNormalCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleVectorCapDuality
import HodgeLean.Foundations.QuotientDuality.ProperCycleEmptyTriadCapDuality
import HodgeLean.Foundations.QuotientDuality.ProperCycleProductSupport

/-! # Fixed ambient orientation in actual normal product cap duality
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- In an actual vector-times-normal product, cap with a fixed ambient orientation identifies supported cohomology with tangential relative homology, using the original triad cap.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, local cap suspension and universal coefficients.
HC no distance; AV milestone no distance. -/
lemma properCycle_oriented_product_cap_bijective
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) [T1Space Y] (y : Y) (p : ℕ) (hp : Even p)
    (z : orientationGroup Y p y)
    (hzgen : Function.Bijective (LinearMap.toSpanSingleton ℚ (orientationGroup Y p y) z))
    (hzero : Module.finrank ℚ (Homology ℚ Y 0) = 1)
    (c : TriadRelativeHomology ℚ (TopCat.of (E × Y))
      (Prod.snd ⁻¹' ({y} : Set Y)ᶜ) {w | w.1 = 0}ᶜ (p + Module.finrank ℝ E))
    (hcgen : Function.Bijective (LinearMap.toSpanSingleton ℚ _ c)) :
    Function.Bijective (fun a : CohomologyWithSupport ℚ (TopCat.of (E × Y))
      (Prod.snd ⁻¹' ({y} : Set Y)) p =>
      triadCapCohomologyLinear ℚ (TopCat.of (E × Y))
        (Prod.snd ⁻¹' ({y} : Set Y)ᶜ) {w | w.1 = 0}ᶜ p (Module.finrank ℝ E) a c) := by
  have hz : z ≠ 0 := by
    intro hz
    exact (one_ne_zero : (1 : ℚ) ≠ 0) (hzgen.1 (by simp [hz]))
  let α := normalizedRelativeCoclass z hz
  let g := properCycle_product_support_cohomology_equiv E Y {y} p
  have hαgen := properCycle_specified_normal_coclass_generates
    (pointComplementPair y) p z hz hzgen
  have hprodgen : Function.Bijective (LinearMap.toSpanSingleton ℚ _ (g α)) := by
    convert g.bijective.comp hαgen using 1
    funext r
    exact (map_smul g r α).symm
  have hnormal := properCycle_empty_triad_cohomology_cap_bijective Y ({y} : Set Y)ᶜ
    p 0 hp α (properCycle_normalized_relative_cap_bijective
      (pointComplementPair y) p z hz hzgen hzero)
  have hproduct := properCycle_vector_product_cap_bijective E Y {y} Set.univ
    isClosed_singleton isClosed_univ p 0 hp α (by rw [Set.compl_univ]; exact hnormal)
  have hfixed : Function.Bijective (triadCapCohomologyLinear ℚ (TopCat.of (E × Y))
      (Prod.snd ⁻¹' ({y} : Set Y)ᶜ) {w | w.1 = 0}ᶜ p (Module.finrank ℝ E) (g α)) := by
    rw [properCycle_product_support_cohomology_equiv_apply]
    change Function.Bijective (triadCapCohomologyLinear ℚ (TopCat.of (E × Y))
      (Prod.snd ⁻¹' ({y} : Set Y)ᶜ) {w | w.1 = 0}ᶜ p (Module.finrank ℝ E)
      (relativeCohomologyMap ℚ p (properCycle_product_support_projection E Y {y}) α))
    have ht : {w : E × Y | w.1 = 0 ∧ w.2 ∈ (Set.univ : Set Y)} =
        {w : E × Y | w.1 = 0} := by ext w; simp only [Set.mem_setOf_eq, Set.mem_univ, and_true]
    rw [ht, zero_add] at hproduct
    exact hproduct
  exact properCycle_bilinear_orientation_swap
    (triadCapCohomologyLinear ℚ (TopCat.of (E × Y))
      (Prod.snd ⁻¹' ({y} : Set Y)ᶜ) {w | w.1 = 0}ᶜ p (Module.finrank ℝ E))
    (g α) c hprodgen hcgen hfixed

end HodgeLean.Foundations.QuotientDuality
