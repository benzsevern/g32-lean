import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalAffineSchemeChart
import HodgeLean.Foundations.Program.SchoenCycleProjectiveSectionEvaluation

/-! # Actual regular sections for the specified affine normal coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations.Program
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual regular coordinate section on the leading projective affine chart. -/
def normalAffineCoordinateSection (k : ℕ) (j : Fin k) :
    Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ),
      (s2e_standardProjectiveAffineOpen (0 : Fin (k + 1))).1) :=
  (s2e_standardProjectiveSectionRingEquiv (0 : Fin (k + 1))).symm
    (s2e_baseChangedChartAlgEquiv.{0, 0} ℂ (0 : Fin (k + 1))
      ((1 : ℂ) ⊗ₜ[ℤ] chartCoordinate.{0} (0 : Fin (k + 1)) j.succ))

/-- The regular normal coordinate section evaluates to the actual homogeneous coordinate ratio. -/
theorem normalAffineCoordinateSection_evaluate (k : ℕ) (j : Fin k)
    (v : CoordinateSpace k) (hv : v 0 ≠ 0) :
    Point.evaluate (s2e_standardProjectiveAffineOpen (0 : Fin (k + 1))).1
      (normalAffineCoordinateSection k j)
      (vectorToComplexPoint v (vector_ne_zero_of_coordinate v 0 hv)) = v j.succ / v 0 := by
  rw [s2e_standardProjectiveSection_evaluate, normalAffineCoordinateSection,
    RingEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply]
  simp only [s2e_standardProjectiveChartEvaluation, AlgHom.liftEquiv_tmul, one_smul,
    RingHom.toIntAlgHom_apply]
  exact s2e_projective_chartCoordinate_eval v 0 j.succ hv

#print axioms normalAffineCoordinateSection
#print axioms normalAffineCoordinateSection_evaluate
end HodgeLean.Foundations.Program.G32Native.EulerModel
