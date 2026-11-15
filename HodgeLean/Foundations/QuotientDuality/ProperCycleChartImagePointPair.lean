import HodgeLean.Foundations.QuotientDuality.ProperCycleTangentialRetractionPair

/-! # Actual point-pair maps into original chart-image neighborhoods
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The original chart on an actual contained neighborhood maps its point pair into the literal chart-image point pair.
Source: OpenPartialHomeomorph.homeomorphOfImageSubsetSource; TopPair.ofSubsetHom.
HC no distance; AV milestone no distance. -/
def properCycle_chart_image_point_pair
    (X : TopCat.{0}) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (z : X) (hzW : z ∈ W)
    (y : Y) (hcenter : e z = (0, y)) :
    pointComplementPair (⟨z, hzW⟩ : W) ⟶
      pointComplementPair (⟨((0 : E), y), ⟨z, hzW, hcenter⟩⟩ : e '' (W : Set X)) := by
  let H : W ≃ₜ e '' (W : Set X) := e.homeomorphOfImageSubsetSource hWe rfl
  exact TopPair.ofSubsetHom
    (TopCat.ofHom ⟨H, H.continuous⟩ : TopCat.of W ⟶ TopCat.of (e '' (W : Set X))) (by
      intro u hu he
      apply hu
      apply H.injective
      apply Subtype.ext
      have hv := congrArg (fun v : e '' (W : Set X) => v.val) he
      change e u.val = ((0 : E), y) at hv
      exact hv.trans hcenter.symm)

end HodgeLean.Foundations.QuotientDuality
