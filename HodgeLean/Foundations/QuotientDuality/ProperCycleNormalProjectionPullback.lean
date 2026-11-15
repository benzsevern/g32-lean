import HodgeLean.Foundations.QuotientDuality.ProperCycleProductSupport

/-! # Original supported pullbacks determined by the actual normal projection
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Maps into an actual product support pair with the same normal projection have the same pullback on every original supported cohomology class.
Source: properCycle_product_support_cohomology_equiv_apply; relativeCohomologyMap_comp; Hatcher, Algebraic Topology, section 2.1.
HC no distance; AV milestone no distance. -/
lemma properCycle_product_support_pullback_eq_of_normal_eq
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (S : Set Y) (P : TopPair.{0})
    (f g : P ⟶ TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' Sᶜ))
    (h : f ≫ properCycle_product_support_projection E Y S =
      g ≫ properCycle_product_support_projection E Y S)
    (n : ℕ) (b : CohomologyWithSupport ℚ (TopCat.of (E × Y)) (Prod.snd ⁻¹' S) n) :
    relativeCohomologyMap ℚ n f b = relativeCohomologyMap ℚ n g b := by
  let F := properCycle_product_support_cohomology_equiv E Y S n
  let β := F.symm b
  have hβ : relativeCohomologyMap ℚ n (properCycle_product_support_projection E Y S) β = b := by
    have he := properCycle_product_support_cohomology_equiv_apply E Y S n β
    exact he.symm.trans (F.apply_symm_apply b)
  have hf := LinearMap.congr_fun
    (relativeCohomologyMap_comp ℚ n f (properCycle_product_support_projection E Y S)) β
  have hg := LinearMap.congr_fun
    (relativeCohomologyMap_comp ℚ n g (properCycle_product_support_projection E Y S)) β
  change relativeCohomologyMap ℚ n (f ≫ properCycle_product_support_projection E Y S) β =
    relativeCohomologyMap ℚ n f (relativeCohomologyMap ℚ n (properCycle_product_support_projection E Y S) β) at hf
  change relativeCohomologyMap ℚ n (g ≫ properCycle_product_support_projection E Y S) β =
    relativeCohomologyMap ℚ n g (relativeCohomologyMap ℚ n (properCycle_product_support_projection E Y S) β) at hg
  rw [hβ] at hf hg
  exact hf.symm.trans ((congrArg (fun t => relativeCohomologyMap ℚ n t β) h).trans hg)

end HodgeLean.Foundations.QuotientDuality
