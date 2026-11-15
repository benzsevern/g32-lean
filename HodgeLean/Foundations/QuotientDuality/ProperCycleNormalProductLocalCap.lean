import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import HodgeLean.Foundations.QuotientDuality.ProperCycleOrientedProductCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadLocalHomology

/-! # Ambient point homology in actual normal product cap duality
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original product triad at any specified normal point has the actual ambient point homology.
Source: Hatcher, Algebraic Topology, section 2.2, open excision for relative singular homology.
HC no distance; AV milestone no distance. -/
def properCycle_normal_product_triad_point_iso
    (E : Type) [TopologicalSpace E] [T1Space E] [Zero E]
    (Y : TopCat.{0}) [T1Space Y] (y : Y) (n : ℕ) :
    TriadRelativeHomology ℚ (TopCat.of (E × Y))
      (Prod.snd ⁻¹' ({y} : Set Y)ᶜ) {w | w.1 = 0}ᶜ n ≅
      orientationGroup (TopCat.of (E × Y)) n (0, y) := by
  apply properCycle_triad_local_homology_iso (TopCat.of (E × Y)) _ _
    (isClosed_singleton.isOpen_compl.preimage continuous_snd)
    ((isClosed_singleton.preimage continuous_fst).isOpen_compl) (0, y) _ n
  ext w
  change (w.2 ≠ y ∨ w.1 ≠ 0) ↔ w ≠ (0, y)
  constructor
  · rintro (h | h) hw
    · exact h (congrArg Prod.snd hw)
    · exact h (congrArg Prod.fst hw)
  · intro hw
    by_cases h : w.1 = 0
    · exact Or.inl (fun hy => hw (Prod.ext h hy))
    · exact Or.inr h

/-- Cap with an actual ambient point orientation is bijective on supported cohomology in a vector-times-normal chart with connected normal fibre.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, cap suspension in actual product coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_normal_product_point_cap_bijective
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) [T1Space Y] [PathConnectedSpace Y] (y : Y) (p : ℕ) (hp : Even p)
    (c : orientationGroup (TopCat.of (E × Y)) (p + Module.finrank ℝ E) (0, y))
    (hc : Function.Bijective (LinearMap.toSpanSingleton ℚ _ c)) :
    Function.Bijective (fun a : CohomologyWithSupport ℚ (TopCat.of (E × Y))
      (Prod.snd ⁻¹' ({y} : Set Y)) p =>
      triadCapCohomologyLinear ℚ (TopCat.of (E × Y))
        (Prod.snd ⁻¹' ({y} : Set Y)ᶜ) {w | w.1 = 0}ᶜ p (Module.finrank ℝ E) a
        ((properCycle_normal_product_triad_point_iso E Y y (p + Module.finrank ℝ E)).inv c)) := by
  let H := properCycle_vector_product_local_homology_iso E Y y p
  let T := properCycle_normal_product_triad_point_iso E Y y (p + Module.finrank ℝ E)
  have hz : Function.Bijective (LinearMap.toSpanSingleton ℚ _ (H.hom c)) := by
    convert H.toLinearEquiv.bijective.comp hc using 1
    funext r
    exact (map_smul H.hom.hom r c).symm
  have ht : Function.Bijective (LinearMap.toSpanSingleton ℚ _ (T.inv c)) := by
    convert T.symm.toLinearEquiv.bijective.comp hc using 1
    funext r
    exact (map_smul T.inv.hom r c).symm
  have hzero : Module.finrank ℚ (Homology ℚ Y 0) = 1 := by
    let e := (asIso (TopCat.singularHomology₀ε Y (ModuleCat.of ℚ ℚ))).toLinearEquiv
    exact e.finrank_eq.trans (Module.finrank_self ℚ)
  exact properCycle_oriented_product_cap_bijective E Y y p hp (H.hom c) hz hzero (T.inv c) ht

end HodgeLean.Foundations.QuotientDuality
