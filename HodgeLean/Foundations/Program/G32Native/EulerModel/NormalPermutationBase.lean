import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalCoordinatePermutation

/-! # The specified projective coordinate action on the original kernel-model base -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual projective homeomorphism induced by the specified homogeneous coordinate permutation. -/
def normalPermutationBaseHomeomorph (k : ℕ) (e : Equiv.Perm (Fin (k + 1))) :
    Projectivization ℂ (ℂ × (Fin k → ℂ)) ≃ₜ
      Projectivization ℂ (ℂ × (Fin k → ℂ)) where
  toEquiv := s2e_projectiveLinearEquiv (normalCoordinatePermutation k e)
  continuous_toFun := by
    apply continuous_coinduced_dom.mpr
    exact isQuotientMap_quotient_mk'.continuous.comp
      (((normalCoordinatePermutation k e).toLinearMap.continuous_of_finiteDimensional.comp
        continuous_subtype_val).subtype_mk
          (fun v => (normalCoordinatePermutation k e).map_ne_zero_iff.mpr v.2))
  continuous_invFun := by
    apply continuous_coinduced_dom.mpr
    exact isQuotientMap_quotient_mk'.continuous.comp
      (((normalCoordinatePermutation k e).symm.toLinearMap.continuous_of_finiteDimensional.comp
        continuous_subtype_val).subtype_mk
          (fun v => (normalCoordinatePermutation k e).symm.map_ne_zero_iff.mpr v.2))

#print axioms normalPermutationBaseHomeomorph
/-- The actual projective permutation retains its specified nonzero homogeneous representative. -/
theorem normalPermutationBaseHomeomorph_mk (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (v : ℂ × (Fin k → ℂ)) (hv : v ≠ 0) :
    normalPermutationBaseHomeomorph k e (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (normalCoordinatePermutation k e v)
        ((normalCoordinatePermutation k e).map_ne_zero_iff.mpr hv) := rfl

#print axioms normalPermutationBaseHomeomorph_mk
/-- The actual coordinate action transports each specified kernel vector into precisely its corresponding kernel fibre. -/
theorem normalCoordinatePermutation_kernel (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1)))
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ))) (a : ℂ × (Fin k → ℂ)) :
    normalCoordinatePermutation k e a ∈
        projectiveNormalKernel k (normalPermutationBaseHomeomorph k e p) ↔
      a ∈ projectiveNormalKernel k p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [normalPermutationBaseHomeomorph_mk, projectiveNormalKernel_mk,
      projectiveNormalKernel_mk, LinearMap.mem_ker, LinearMap.mem_ker,
      homogeneousNormalEvaluation_permutation]

#print axioms normalCoordinatePermutation_kernel
/-- The inverse actual projective coordinate action retains the inverse linear homogeneous representative. -/
theorem normalPermutationBaseHomeomorph_symm_mk (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (v : ℂ × (Fin k → ℂ)) (hv : v ≠ 0) :
    (normalPermutationBaseHomeomorph k e).symm (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ ((normalCoordinatePermutation k e).symm v)
        ((normalCoordinatePermutation k e).symm.map_ne_zero_iff.mpr hv) := rfl

#print axioms normalPermutationBaseHomeomorph_symm_mk
end HodgeLean.Foundations.Program.G32Native.EulerModel
