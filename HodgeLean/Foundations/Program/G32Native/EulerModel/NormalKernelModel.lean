import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Determinant

/-! # Real determinant of the conjugate normal-coordinate model -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Coordinatewise conjugation in the real vector space underlying the normal model. -/
def normalConjugation (k : ℕ) : (Fin k → ℂ) →ₗ[ℝ] (Fin k → ℂ) :=
  LinearMap.pi fun i => Complex.conjAe.toLinearEquiv.toLinearMap.comp (LinearMap.proj i)

/-- Each conjugated complex normal coordinate contributes one negative real determinant. -/
theorem normalConjugation_det (k : ℕ) :
    LinearMap.det (normalConjugation k) = (-1 : ℝ) ^ k := by
  rw [normalConjugation, LinearMap.det_pi]
  simp only [Complex.det_conjAe, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

#print axioms normalConjugation_det
/-- Negating the conjugate coordinates has the same real determinant in complex rank k. -/
theorem neg_normalConjugation_det (k : ℕ) :
    LinearMap.det (-normalConjugation k) = (-1 : ℝ) ^ k := by
  rw [show -normalConjugation k = (-1 : ℝ) • normalConjugation k from (neg_one_smul ℝ _).symm,
    LinearMap.det_smul, normalConjugation_det]
  simp only [finrank_real_of_complex, Module.finrank_pi, Fintype.card_fin, pow_mul,
    neg_one_sq, one_pow, one_mul]

#print axioms neg_normalConjugation_det
/-- Applying the real conjugate-coordinate map twice restores the same vector. -/
theorem normalConjugation_involutive (k : ℕ) : Function.Involutive (normalConjugation k) := by
  intro z
  funext i
  simp [normalConjugation]

#print axioms normalConjugation_involutive
end HodgeLean.Foundations.Program.G32Native.EulerModel
