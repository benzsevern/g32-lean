import HodgeLean.Foundations.Abdulali.VolumeContraction

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The normalized covector records the sign of a permutation of contracted slots. -/
theorem normalizedVolumeCovector_perm
    (σ : Equiv.Perm (Fin (Module.finrank ℂ V)))
    (z : ⨂[ℂ]^(Module.finrank ℂ V) V) :
    normalizedVolumeCovector (SchurWeyl.permRep ℂ V _ σ z) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * normalizedVolumeCovector z := by
  classical
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul, normalizedVolumeCovector, LinearMap.smul_apply,
      SchurWeyl.permRep_tprod, SchurWeyl.detTensor_eq,
      SchurWeyl.dualDistrib_antisymTensor_tprod_perm,
      Equiv.Perm.sign_symm, smul_eq_mul]
    ring
  | add x y hx hy =>
    simp only [map_add, hx, hy, mul_add]

/-- A tensor symmetric in two distinct contracted slots has zero volume evaluation. -/
theorem normalizedVolumeCovector_eq_zero_of_swap
    (i j : Fin (Module.finrank ℂ V)) (hij : i ≠ j)
    (z : ⨂[ℂ]^(Module.finrank ℂ V) V)
    (hz : SchurWeyl.permRep ℂ V _ (Equiv.swap i j) z = z) :
    normalizedVolumeCovector z = 0 := by
  have h := normalizedVolumeCovector_perm (Equiv.swap i j) z
  rw [hz, Equiv.Perm.sign_swap hij] at h
  norm_num only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at h
  linear_combination (1 / 2 : ℂ) * h

end HodgeLean.Foundations.Abdulali
