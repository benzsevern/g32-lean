import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelCharts
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-! # The conjugate section in the projective evaluation kernel -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual linear coordinate frame of the projective evaluation kernel. -/
def normalKernelFrame (k : ℕ) (z : Fin k → ℂ) :
    (Fin k → ℂ) ≃ₗ[ℂ] LinearMap.ker (normalEvaluation k z) :=
  LinearEquiv.ofBijective (normalKernelChart k z) (normalKernelChart_bijective k z)

/-- The conjugate local section, expressed as a vector in the actual evaluation kernel. -/
def normalKernelSection (k : ℕ) (z : Fin k → ℂ) : LinearMap.ker (normalEvaluation k z) :=
  normalKernelChart k z (-normalConjugation k z)

/-- The coefficients of the kernel section are exactly the negated conjugate coordinates. -/
theorem normalKernelSection_coefficients (k : ℕ) (z : Fin k → ℂ) :
    (normalKernelFrame k z).symm (normalKernelSection k z) = -normalConjugation k z := by
  change (normalKernelFrame k z).symm
    ((normalKernelFrame k z) (-normalConjugation k z)) = _
  exact LinearEquiv.symm_apply_apply _ _

#print axioms normalKernelSection_coefficients
/-- The conjugate section has exactly the chart origin as its zero. -/
theorem normalKernelSection_zero_iff (k : ℕ) (z : Fin k → ℂ) :
    normalKernelSection k z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have hc := congrArg (normalKernelFrame k z).symm hz
    rw [normalKernelSection_coefficients, map_zero] at hc
    apply (normalConjugation_involutive k).injective
    simpa only [map_zero] using neg_eq_zero.mp hc
  · rintro rfl
    simp [normalKernelSection]

#print axioms normalKernelSection_zero_iff
/-- The real derivative of the section coefficients is the negated conjugation map. -/
theorem normalKernelSection_fderiv (k : ℕ) (z : Fin k → ℂ) :
    fderiv ℝ (fun w => (normalKernelFrame k w).symm (normalKernelSection k w)) z =
      (-normalConjugation k).toContinuousLinearMap := by
  have hf : (fun w => (normalKernelFrame k w).symm (normalKernelSection k w)) =
      (-normalConjugation k).toContinuousLinearMap := by
    funext w
    exact normalKernelSection_coefficients k w
  rw [hf]
  exact ContinuousLinearMap.fderiv _

#print axioms normalKernelSection_fderiv
/-- The real determinant at the unique zero is the required parity sign in the kernel model. -/
theorem normalKernelSection_derivative_det (k : ℕ) :
    LinearMap.det
      (fderiv ℝ (fun w => (normalKernelFrame k w).symm (normalKernelSection k w))
        (0 : Fin k → ℂ)).toLinearMap = (-1 : ℝ) ^ k := by
  rw [normalKernelSection_fderiv]
  change LinearMap.det (-normalConjugation k) = (-1 : ℝ) ^ k
  exact neg_normalConjugation_det k

#print axioms normalKernelSection_derivative_det
end HodgeLean.Foundations.Program.G32Native.EulerModel
