import HodgeLean.Foundations.TubularEuler.ProjectorPointRecoveryHelpers

/-! # Injectivity of the actual projective Hermitian projector

A single nonzero diagonal entry recovers the same homogeneous point from
either of two equal projector matrices.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ComplexPoint AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.TubularEuler

/-- The homogeneous Hermitian projector separates actual scheme projective
points, including points lying in different affine charts initially.
Source: `projectorRecoveredPoint_coordinates` and
`hermitianProjector_ratio`; Griffiths–Harris, Principles of Algebraic
Geometry, chapter 1, section 2, homogeneous projective coordinates.
HC no distance; AV milestone no distance. -/
theorem projectiveHermitianProjector_injective (N : ℕ) :
    Function.Injective (projectiveHermitianProjector N) := by
  intro p q hpq
  obtain ⟨⟨v, hv⟩, rfl⟩ := surjective_vectorToComplexPoint p
  obtain ⟨⟨w, hw⟩, rfl⟩ := surjective_vectorToComplexPoint q
  change projectiveHermitianProjector N
    (projectivizationToComplexPoint (Projectivization.mk ℂ v hv)) =
      projectiveHermitianProjector N
        (projectivizationToComplexPoint (Projectivization.mk ℂ w hw)) at hpq
  rw [projectiveHermitianProjector_coordinates,
    projectiveHermitianProjector_coordinates] at hpq
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hvi : hermitianProjector v i i ≠ 0 := by
    intro hz
    have hr := hermitianProjector_ratio v i hi i
    rw [hz, div_zero, div_self hi] at hr
    exact zero_ne_one hr
  have hwi : w i ≠ 0 := by
    intro hz
    apply hvi
    rw [hpq]
    simp [hermitianProjector, hz]
  calc
    vectorToComplexPoint v hv = projectorRecoveredPoint i (hermitianProjector v) :=
      (projectorRecoveredPoint_coordinates v hv i hi).symm
    _ = projectorRecoveredPoint i (hermitianProjector w) :=
      congrArg (projectorRecoveredPoint i) hpq
    _ = vectorToComplexPoint w hw := projectorRecoveredPoint_coordinates w hw i hwi

#print axioms projectiveHermitianProjector_injective

end HodgeLean.Foundations.TubularEuler
