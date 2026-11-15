import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectiveEmbeddingNonvanishing
import HodgeLean.Foundations.QuotientDuality.RetainedCycleComponentPresentation
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicComponentComparison

/-! # Projective nonvanishing of the literal intrinsic prime image -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- A projective middle prime has nonzero intrinsic fundamental-class image in its ambient space. -/
lemma retained_projective_prime_image_ne_zero
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (ξ : X.left) (hc : Order.coheight ξ = k) :
    properCycle_intrinsic_component X k ξ ≠ 0 := by
  rcases ‹IsProjective X.hom›.nonempty_presentation with ⟨D⟩
  let V := properCycle_component_over X ξ
  let E := retained_component_projective_presentation X D ξ
  have hdV := properCycle_middle_component_dimension X k hdim ξ hc
  have hn := retained_projective_presentation_image_nonzero V E k hdV
  rw [properCycle_intrinsic_component_eq_image X k ξ hdV]
  intro hz
  apply hn
  change properCycle_intrinsic_image (retainedPresentationInclusion V E) k
    (properCycle_intrinsic_class V k hdV) = 0
  have he : retainedPresentationInclusion V E =
      properCycle_component_over_inclusion X ξ ≫ retainedPresentationInclusion X D := by
    apply Over.OverMorphism.ext
    rfl
  rw [he, properCycle_intrinsic_image_comp, hz]
  exact map_zero _

end HodgeLean.Foundations.QuotientDuality
