import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A smooth complex closed immersion has simultaneous standard smooth
affine charts on the ambient scheme and its actual inverse image. -/
theorem s2e_closedImmersion_simultaneous_standardSmooth_charts
    (Q W : Over (Spec ↧ℂ)) (n d : ℕ)
    [SmoothOfRelativeDimension n Q.hom] [SmoothOfRelativeDimension d W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (x : Q.left) :
    ∃ V : W.left.Opens, IsAffineOpen V ∧ ι.left x ∈ V ∧
      IsAffineOpen (ι.left ⁻¹ᵁ V) ∧
      (W.hom.appLE ⊤ V (by simp)).hom.IsStandardSmoothOfRelativeDimension d ∧
      (Q.hom.appLE ⊤ (ι.left ⁻¹ᵁ V) (by simp)).hom.IsStandardSmoothOfRelativeDimension n := by
  obtain ⟨V, hV, hxV, hVs⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension
      (f := W.hom) (d := d) (ι.left x)
  obtain ⟨T, hT, hxT, hTs⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension
      (f := Q.hom) (d := n) x
  have hP : IsAffineOpen (ι.left ⁻¹ᵁ V) := hV.preimage ι.left
  obtain ⟨g, t, hgt, hx⟩ := exists_basicOpen_le_affine_inter hP hT x ⟨hxV, hxT⟩
  obtain ⟨f, hf⟩ := ι.left.app_surjective V hV g
  have hpre : ι.left ⁻¹ᵁ (W.left.basicOpen f) = Q.left.basicOpen t := by
    rw [Scheme.preimage_basicOpen, hf, hgt]
  refine ⟨W.left.basicOpen f, hV.basicOpen f, ?_, (hV.basicOpen f).preimage ι.left,
    isStandardSmoothOfRelativeDimension_appLE_basicOpen W.hom hV f hVs, ?_⟩
  · change x ∈ ι.left ⁻¹ᵁ (W.left.basicOpen f)
    rw [hpre, ← hgt]
    exact hx
  · rw [hpre]
    exact isStandardSmoothOfRelativeDimension_appLE_basicOpen Q.hom hT t hTs

end HodgeLean.Foundations.Program
