import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelSection
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! # The global projective evaluation kernel -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Evaluation on an arbitrary homogeneous coordinate vector. -/
def homogeneousNormalEvaluation (k : ℕ) (v : ℂ × (Fin k → ℂ)) :
    (ℂ × (Fin k → ℂ)) →ₗ[ℂ] ℂ :=
  v.1 • LinearMap.fst ℂ ℂ (Fin k → ℂ) +
    ∑ i : Fin k, v.2 i • (LinearMap.proj i).comp (LinearMap.snd ℂ ℂ (Fin k → ℂ))

/-- Homogeneous evaluation uses the actual coordinate pairing. -/
theorem homogeneousNormalEvaluation_apply (k : ℕ) (v a : ℂ × (Fin k → ℂ)) :
    homogeneousNormalEvaluation k v a = v.1 * a.1 + ∑ i, v.2 i * a.2 i := by
  simp only [homogeneousNormalEvaluation, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.fst_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.snd_apply, smul_eq_mul]

#print axioms homogeneousNormalEvaluation_apply
/-- Scaling the homogeneous vector scales the evaluation map by the same scalar. -/
theorem homogeneousNormalEvaluation_smul (k : ℕ) (v : ℂ × (Fin k → ℂ)) (a : ℂ) :
    homogeneousNormalEvaluation k (a • v) = a • homogeneousNormalEvaluation k v := by
  apply LinearMap.ext
  intro w
  simp [homogeneousNormalEvaluation_apply, smul_eq_mul, mul_add, Finset.mul_sum, mul_assoc]

#print axioms homogeneousNormalEvaluation_smul
/-- The evaluation kernel is independent of a nonzero homogeneous scaling. -/
theorem homogeneousNormalKernel_smul (k : ℕ) (v : ℂ × (Fin k → ℂ))
    (a : ℂ) (ha : a ≠ 0) :
    LinearMap.ker (homogeneousNormalEvaluation k (a • v)) =
      LinearMap.ker (homogeneousNormalEvaluation k v) := by
  ext w
  simp only [LinearMap.mem_ker, homogeneousNormalEvaluation_smul,
    LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, ha, false_or]

#print axioms homogeneousNormalKernel_smul
/-- The evaluation kernel attached to a projective line, independently of its representative. -/
def projectiveNormalKernel (k : ℕ)
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ))) : Submodule ℂ (ℂ × (Fin k → ℂ)) :=
  Projectivization.lift (fun v => LinearMap.ker (homogeneousNormalEvaluation k v.1))
    (by
      intro v w a ha
      have ha0 : a ≠ 0 := by
        intro hzero
        apply v.2
        rw [ha, hzero, zero_smul]
      rw [ha]
      exact homogeneousNormalKernel_smul k w.1 a ha0) p

/-- The global kernel specializes to the actual homogeneous evaluation kernel. -/
theorem projectiveNormalKernel_mk (k : ℕ) (v : ℂ × (Fin k → ℂ)) (hv : v ≠ 0) :
    projectiveNormalKernel k (Projectivization.mk ℂ v hv) =
      LinearMap.ker (homogeneousNormalEvaluation k v) := by
  rfl

#print axioms projectiveNormalKernel_mk
end HodgeLean.Foundations.Program.G32Native.EulerModel
