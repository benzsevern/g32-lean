import HodgeLean.Foundations.Program.SchoenTransferQ3SmoothOpen
import HodgeLean.Foundations.Program.SchoenFiniteMorphisms
import HodgeLean.Adapters.IntersectionProductScaf

/-! Flatness on the entire retained smooth ambient open. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Restricting the finite surjection to any smooth target open gives flatness
of the specified restricted map. -/
theorem s4_q3_finite_flat_over_smooth_open
    {X W : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsIntegral W.left]
    (q : X ⟶ W) [IsFinite q.left] [Surjective q.left]
    (U : W.left.Opens) (hU : Smooth (U.ι ≫ W.hom)) : Flat (q.left ∣_ U) := by
  let V := q.left ⁻¹ᵁ U
  let XU : Over (Spec ↧ℂ) := Over.mk (V.ι ≫ X.hom)
  let WU : Over (Spec ↧ℂ) := Over.mk (U.ι ≫ W.hom)
  let f : XU ⟶ WU := Over.homMk (q.left ∣_ U) (by
    change (q.left ∣_ U) ≫ U.ι ≫ W.hom = V.ι ≫ X.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w q])
  cases isEmpty_or_nonempty V.toScheme with
  | inl h => exact inferInstance
  | inr h =>
    letI : Nonempty U.toScheme := Nonempty.map (q.left ∣_ U) h
    letI : IsIntegral XU.left := inferInstanceAs (IsIntegral V.toScheme)
    letI : IsIntegral WU.left := inferInstanceAs (IsIntegral U.toScheme)
    letI : Smooth WU.hom := hU
    letI : Smooth XU.hom := inferInstanceAs (Smooth (V.ι ≫ X.hom))
    letI : IsFinite f.left := inferInstanceAs (IsFinite (q.left ∣_ U))
    letI : Surjective f.left := MorphismProperty.of_isPullback
      (P := @Surjective) (isPullback_morphismRestrict q.left U).flip inferInstance
    exact IntersectionProductScaf_finite_smooth_flat XU WU f

/-- The canonical smooth locus is a dense flat neighbourhood containing every
retained support prime; it is not shrunk by generic flatness. -/
theorem s4_q3_retained_flat_open
    {X W : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsIntegral W.left]
    [LocallyOfFinitePresentation W.hom]
    (q : X ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (z : AlgebraicCycle W.left ℚ)
    (hz : ∀ x ∈ z.support, ∃ V : W.left.Opens, x ∈ V ∧ Smooth (V.ι ≫ W.hom)) :
    Dense (W.hom.smoothLocus : Set W.left) ∧
      Smooth (W.hom.smoothLocus.ι ≫ W.hom) ∧
      Flat (q.left ∣_ W.hom.smoothLocus) ∧
      ∀ x ∈ z.support, x ∈ W.hom.smoothLocus := by
  obtain ⟨hdense, hsmooth, hmem⟩ := s4_q3_retained_smooth_open W z hz
  letI : Surjective q.left := ⟨s2_surjective_of_point_surjective q hqsurj⟩
  exact ⟨hdense, hsmooth, s4_q3_finite_flat_over_smooth_open q _ hsmooth, hmem⟩

end HodgeLean.Foundations.Program
