import HodgeLean.Foundations.Program.G32Native.EulerModel.GlobalNormalTopology

/-! # The normalized chart of the global projective kernel model -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators ComplexConjugate
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The normalized first projective chart in the global normal model. -/
def normalProjectiveChart (k : ℕ) (z : Fin k → ℂ) : Projectivization ℂ (ℂ × (Fin k → ℂ)) :=
  Projectivization.mk ℂ (1, z) (by
    intro h
    exact one_ne_zero (congrArg (fun w : ℂ × (Fin k → ℂ) => w.1) h))

/-- The global evaluation kernel restricts to the already specified local kernel. -/
theorem projectiveNormalKernel_chart (k : ℕ) (z : Fin k → ℂ) :
    projectiveNormalKernel k (normalProjectiveChart k z) = LinearMap.ker (normalEvaluation k z) := by
  unfold normalProjectiveChart
  rw [projectiveNormalKernel_mk]
  congr 1
  apply LinearMap.ext
  intro a
  rw [homogeneousNormalEvaluation_apply, normalEvaluation_apply, one_mul]

#print axioms projectiveNormalKernel_chart
/-- The global section has the conjugate local coefficients with its Hermitian denominator. -/
theorem projectiveNormalSectionVector_chart (k : ℕ) (z : Fin k → ℂ) :
    (projectiveNormalSectionVector k (normalProjectiveChart k z)).2 =
      (normalLengthSq k (1, z) : ℂ)⁻¹ • (-normalConjugation k z) := by
  unfold normalProjectiveChart
  rw [projectiveNormalSectionVector_mk]
  funext i
  simp [homogeneousNormalSection, normalConjugation, smul_eq_mul]

#print axioms projectiveNormalSectionVector_chart
end HodgeLean.Foundations.Program.G32Native.EulerModel
