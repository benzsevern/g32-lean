import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

/-! # Actual smooth affine neighborhoods of the generic point -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Every prescribed generic base neighborhood contains an actual affine smooth neighborhood of the original intrinsic dimension.
Source: EGA IV, 17.5.1, generic smoothness over a perfect field; EGA IV, 5.6.5, dimension of a nonempty open.
HC no distance; AV milestone no distance. -/
lemma properCycle_smooth_affine_generic_neighborhood
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [LocallyOfFiniteType Y.hom]
    (d : ℕ) (hdim : TopologicalSpace.dim Y.left = d)
    (U : Y.left.Opens) (hgU : genericPoint Y.left ∈ U) :
    ∃ W : Y.left.Opens, IsAffineOpen W ∧ genericPoint Y.left ∈ W ∧ W ≤ U ∧
      SmoothOfRelativeDimension d (openScheme Y W).hom := by
  have hgs : genericPoint Y.left ∈ Y.hom.smoothLocus :=
    Y.hom.genericPoint_mem_smoothLocus_of_perfectField
  obtain ⟨W, hW, hgW, hWsub⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint Y.left ∈ U ⊓ Y.hom.smoothLocus from ⟨hgU, hgs⟩)
  let Z := openScheme Y W
  letI : Nonempty W := ⟨⟨genericPoint Y.left, hgW⟩⟩
  letI : Nonempty Z.left := inferInstanceAs (Nonempty W.toScheme)
  letI : IsIntegral Z.left := isIntegral_of_isOpenImmersion W.ι
  letI : LocallyOfFiniteType Z.hom := by
    change LocallyOfFiniteType (W.ι ≫ Y.hom)
    infer_instance
  letI : Smooth Z.hom := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    change (W.ι ≫ Y.hom).smoothLocus = ⊤
    rw [← Scheme.Hom.preimage_smoothLocus_eq W.ι Y.hom]
    apply top_unique
    intro z _
    exact (hWsub z.property).2
  have hdimZ : TopologicalSpace.dim Z.left = d :=
    (properCycle_nonempty_open_dimension Y W).trans hdim
  have hs : SmoothOfRelativeDimension d Z.hom := by
    rw [← hdimZ]
    infer_instance
  exact ⟨W, hW, hgW, fun _ h => (hWsub h).1, hs⟩

end HodgeLean.Foundations.QuotientDuality
