import HodgeLean.Foundations.Program.SchoenCycleProjCoordinateMaps
import HodgeLean.Foundations.Program.SchoenCycleProjectiveBaseChange

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- The support of the residue intersection is the homogeneous coordinate zero locus.
Source: Schoen (1988), Lemma 2.3(vi), printed pp. 13–14; Lemma 2.4 proof, printed p. 15. -/
theorem s2e_intersection_support_coordinates (k : ℕ) (T : Finset (Fin (k + 1)))
    (y : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)) :
    y ∈ (s2e_s2b_intersectionIdeal k T).support ↔
      ∀ j ∈ T, (MvPolynomial.X j : MvPolynomial (Fin (k + 1)) (ULift.{0} ℤ)) ∈
        ((pullback.snd (terminal.from (Spec ↧ℂ))
          (terminal.from (Proj (UniversalGrading.{0} k)))) y).asHomogeneousIdeal.toIdeal := by
  constructor
  · intro hy j hj
    have hle : s2e_s2b_residueIdeal k j ≤ s2e_s2b_intersectionIdeal k T :=
      le_iSup_of_le j (le_iSup_of_le hj le_rfl)
    have hz := Scheme.IdealSheafData.support_antitone hle hy
    change y ∈ ((s2e_s2b_residueIdeal k j).support : Set _) at hz
    rw [s2e_s2b_residueIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hz
    change ¬ ¬ ((MvPolynomial.X j : MvPolynomial (Fin (k + 1)) (ULift.{0} ℤ)) ∈
      ((pullback.snd (terminal.from (Spec ↧ℂ))
        (terminal.from (Proj (UniversalGrading.{0} k)))) y).asHomogeneousIdeal.toIdeal) at hz
    exact not_not.mp hz
  · intro h
    rw [s2e_s2b_intersectionIdeal, Scheme.IdealSheafData.support_iSup]
    apply TopologicalSpace.Closeds.mem_iInf.mpr
    intro j
    rw [Scheme.IdealSheafData.support_iSup]
    apply TopologicalSpace.Closeds.mem_iInf.mpr
    intro hj
    change y ∈ ((s2e_s2b_residueIdeal k j).support : Set _)
    rw [s2e_s2b_residueIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change ¬ ¬ ((MvPolynomial.X j : MvPolynomial (Fin (k + 1)) (ULift.{0} ℤ)) ∈
      ((pullback.snd (terminal.from (Spec ↧ℂ))
        (terminal.from (Proj (UniversalGrading.{0} k)))) y).asHomogeneousIdeal.toIdeal)
    exact not_not.mpr (h j hj)

/-- Insert zeros in the selected coordinates on complex projective space.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
def s2e_coordinateSubspaceInclusion (k : ℕ) (T : Finset (Fin (k + 1))) :
    ProjectiveSpace {j : Fin (k + 1) // j ∉ T} (Spec ↧ℂ) ⟶
      ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) :=
  s2e_projectiveBaseChange (s2e_integralCoordinateInclusion
    (⟨Subtype.val, Subtype.val_injective⟩ : {j : Fin (k + 1) // j ∉ T} ↪ Fin (k + 1)))

/-- The complex retained-coordinate morphism is a closed immersion.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_coordinateSubspaceInclusion_isClosedImmersion (k : ℕ)
    (T : Finset (Fin (k + 1))) : IsClosedImmersion (s2e_coordinateSubspaceInclusion k T) := by
  let e : {j : Fin (k + 1) // j ∉ T} ↪ Fin (k + 1) := ⟨Subtype.val, Subtype.val_injective⟩
  letI := s2e_integralCoordinateInclusion_isClosedImmersion e
  exact s2e_projectiveBaseChange_isClosedImmersion (s2e_integralCoordinateInclusion e)

/-- The complex coordinate immersion has exactly the support of the residue intersection.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_coordinateSubspaceInclusion_range (k : ℕ) (T : Finset (Fin (k + 1))) :
    Set.range (s2e_coordinateSubspaceInclusion k T) =
      ((s2e_s2b_intersectionIdeal k T).support : Set _) := by
  let e : {j : Fin (k + 1) // j ∉ T} ↪ Fin (k + 1) := ⟨Subtype.val, Subtype.val_injective⟩
  have h := s2e_projectiveBaseChange_range (s2e_integralCoordinateInclusion e)
  have hr := s2e_integralCoordinateInclusion_range k T
  rw [hr] at h
  exact h.trans (by
    ext y
    exact (s2e_intersection_support_coordinates k T y).symm)

/-- The retained coordinate indices have the dimension prescribed by the residue count.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_retainedCoordinate_equiv (k : ℕ) (T : Finset (Fin (k + 1)))
    (hT : T.card ≤ k) :
    Nonempty ({j : Fin (k + 1) // j ∉ T} ≃ Fin (k - T.card + 1)) := by
  classical
  refine ⟨Fintype.equivOfCardEq ?_⟩
  simp only [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  omega

end HodgeLean.Foundations.Program
