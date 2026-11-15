import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelModel

/-! # Coordinate frames for the projective evaluation kernel -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Evaluation on the normalized projective vector `(1,z)`. -/
def normalEvaluation (k : ℕ) (z : Fin k → ℂ) : (ℂ × (Fin k → ℂ)) →ₗ[ℂ] ℂ :=
  LinearMap.fst ℂ ℂ (Fin k → ℂ) +
    ∑ i : Fin k, z i • (LinearMap.proj i).comp (LinearMap.snd ℂ ℂ (Fin k → ℂ))

/-- The evaluation kernel has the actual linear equation on this chart. -/
theorem normalEvaluation_apply (k : ℕ) (z : Fin k → ℂ) (a : ℂ × (Fin k → ℂ)) :
    normalEvaluation k z a = a.1 + ∑ i, z i * a.2 i := by
  simp only [normalEvaluation, LinearMap.add_apply, LinearMap.fst_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.snd_apply, smul_eq_mul]

#print axioms normalEvaluation_apply
/-- The standard frame in the actual kernel of projective evaluation. -/
def normalKernelChart (k : ℕ) (z : Fin k → ℂ) :
    (Fin k → ℂ) →ₗ[ℂ] LinearMap.ker (normalEvaluation k z) :=
  ((-(∑ i : Fin k, z i • (LinearMap.proj i : (Fin k → ℂ) →ₗ[ℂ] ℂ))).prod
    (LinearMap.id : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ))).codRestrict _ (by
      intro a
      rw [LinearMap.mem_ker, normalEvaluation_apply]
      simp)

/-- The kernel frame retains the tangential coordinates and solves the first coordinate. -/
theorem normalKernelChart_val (k : ℕ) (z a : Fin k → ℂ) :
    (normalKernelChart k z a).1 = (-(∑ i, z i * a i), a) := by
  simp [normalKernelChart]

#print axioms normalKernelChart_val
/-- Every evaluation-kernel vector has a unique coefficient vector in this frame. -/
theorem normalKernelChart_bijective (k : ℕ) (z : Fin k → ℂ) :
    Function.Bijective (normalKernelChart k z) := by
  constructor
  · intro a b h
    have h' := congrArg (fun v : LinearMap.ker (normalEvaluation k z) => v.1.2) h
    simpa only [normalKernelChart_val] using h'
  · intro a
    refine ⟨a.1.2, ?_⟩
    apply Subtype.ext
    rw [normalKernelChart_val]
    apply Prod.ext
    · have ha := a.property
      rw [LinearMap.mem_ker, normalEvaluation_apply] at ha
      exact (eq_neg_iff_add_eq_zero.mpr ha).symm
    · rfl

#print axioms normalKernelChart_bijective
end HodgeLean.Foundations.Program.G32Native.EulerModel
