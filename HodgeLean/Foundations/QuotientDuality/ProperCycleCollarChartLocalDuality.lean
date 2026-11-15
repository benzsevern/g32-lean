import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartLocalCapComparison

/-! # Actual collar local duality for the original contractible normal product
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual collar local support cap is bijective on the original normal-product supported classes, with the actual ambient orientation generator and a contractible normal fibre.
Source: ProperCycleSupportCollar.chart_local_support_cap_comparison; properCycle_normal_product_support_cap_bijective.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_local_support_cap_bijective
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S) (hS : IsClosed S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Y : TopCat.{0}) [T1Space Y] [ContractibleSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) (p : ℕ) (hp : Even p)
    (c : orientationGroup (TopCat.of W) (p + Module.finrank ℝ E) ⟨z.val, hzW⟩)
    (hc : Function.Bijective (LinearMap.toSpanSingleton ℚ _ c)) :
    Function.Bijective (C.chart_local_support_cap hS E Y e W hWe hWN hR y hflat z hzW hcenter
      p (Module.finrank ℝ E) c) := by
  let G := relativeHomologyMap ℚ (p + Module.finrank ℝ E)
    (properCycle_chart_image_point_pair X E Y e W hWe z.val hzW y hcenter ≫
      properCycle_product_neighborhood_point_pair E Y y (e '' (W : Set X))
        ⟨z.val, hzW, hcenter⟩)
  have hG : Function.Bijective G := by
    dsimp only [G]
    rw [← C.chart_retraction_point_map_eq E Y e W hWe hWN hR y hflat z hzW hcenter]
    exact C.chart_retraction_point_map_bijective E Y e W hWe hWN hR y hflat z hzW hcenter _
  have hGc : Function.Bijective (LinearMap.toSpanSingleton ℚ _ (G c)) := by
    convert hG.comp hc using 1
    funext r
    exact (map_smul G r c).symm
  have hm := properCycle_normal_product_support_cap_bijective E Y y p hp (G c) hGc
  let F := relativeHomologyMap ℚ (Module.finrank ℝ E)
    (properCycle_flat_support_point_pair X S e y hflat z (hWe hzW) (congrArg Prod.fst hcenter))
  have hF : Function.Bijective F :=
    properCycle_flat_support_point_pair_bijective X S e y hflat z (hWe hzW) (congrArg Prod.fst hcenter) _
  have hcomp : F ∘ C.chart_local_support_cap hS E Y e W hWe hWN hR y hflat z hzW hcenter
      p (Module.finrank ℝ E) c = properCycle_normal_product_support_cap E Y y p (G c) := by
    funext a
    exact C.chart_local_support_cap_comparison hS E Y e W hWe hWN hR y hflat z hzW hcenter p c a
  rw [← hcomp] at hm
  exact (Function.Bijective.of_comp_iff' hF _).mp hm

end HodgeLean.Foundations.QuotientDuality
