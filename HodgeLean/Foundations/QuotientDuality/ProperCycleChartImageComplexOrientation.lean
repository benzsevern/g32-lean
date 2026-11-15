import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenPointExcisionInverse
import HodgeLean.Foundations.QuotientDuality.ProperCycleChartImagePointPair
import HodgeLean.Foundations.QuotientDuality.ProperCyclePartialChartOrientation

/-! # The original compressed orientation through actual chart-image point maps
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Original point excision followed by the actual chart-image point map retains the specified compressed complex orientation.
Source: properCycle_restricted_product_chart_orientation; properCycle_open_local_homology_inverse_map.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_image_complex_orientation
    (X : TopCat.{0}) [T1Space X] (r d : ℕ)
    (e : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin d → ℂ))) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (z : X) (hzW : z ∈ W) (hcenter : e z = (0, 0)) :
    let L : ((Fin r → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (r+d) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq
        (by simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin])
    let φ := e.trans L.toHomeomorph.toOpenPartialHomeomorph
    relativeHomologyMap ℚ (2*(r+d))
      (properCycle_chart_image_point_pair X (Fin r → ℂ) (TopCat.of (Fin d → ℂ))
        e W hWe z hzW 0 hcenter ≫
        properCycle_product_neighborhood_point_pair (Fin r → ℂ) (TopCat.of (Fin d → ℂ))
          0 (e '' (W : Set X)) ⟨z, hzW, hcenter⟩)
      ((properCycle_open_local_homology_iso X W ⟨z, hzW⟩ (2*(r+d))).inv.hom
        (localClassOfChart (r+d) φ z ⟨hWe hzW, Set.mem_univ _⟩)) =
      properCycle_complex_product_standard_orientation r d := by
  dsimp only
  let P : neighborhoodPointComplementPair (W : Set X) z ≅
      pointComplementPair (⟨z, hzW⟩ : W) :=
    TopPair.isoOfSubset (Homeomorph.refl W) (by
      intro u
      change u ≠ ⟨z, hzW⟩ ↔ u.val ≠ z
      exact not_congr Subtype.ext_iff)
  let f := properCycle_chart_image_point_pair X (Fin r → ℂ) (TopCat.of (Fin d → ℂ))
    e W hWe z hzW 0 hcenter ≫
    properCycle_product_neighborhood_point_pair (Fin r → ℂ) (TopCat.of (Fin d → ℂ))
      0 (e '' (W : Set X)) ⟨z, hzW, hcenter⟩
  let fP : neighborhoodPointComplementPair (W : Set X) z ⟶
      pointComplementPair ((0, 0) : (Fin r → ℂ) × (Fin d → ℂ)) :=
    TopPair.ofSubsetHom
      (TopCat.ofHom ⟨fun w => e w.val, (e.continuousOn.mono hWe).domRestrict⟩)
      (fun w hw he => hw (e.injOn (hWe w.property) (hWe hzW) (he.trans hcenter.symm)))
  have hp : P.hom ≫ f = fP := by ext u : 2 <;> rfl
  rw [properCycle_open_local_homology_inverse_map]
  change relativeHomologyMap ℚ (2*(r+d)) f (relativeHomologyMap ℚ (2*(r+d)) P.hom _) = _
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, hp]
  exact properCycle_restricted_product_chart_orientation r d e z (hWe hzW) hcenter
    (W : Set X) hWe W.isOpen hzW

end HodgeLean.Foundations.QuotientDuality
