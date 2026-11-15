import HodgeLean.Foundations.Abdulali.InverseFormDiagonal
import HodgeLean.Foundations.Program.MilneTensorCopiesOne

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The base quadratic fixed space is the inverse-form line, in every dimension. -/
theorem orthogonal_base_quadratics_eq_inverseForm_span
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) :
    m1b_fixed (m1b_isometries B) 2 = Submodule.span ℂ {inverseFormTensor B hB hs} := by
  classical
  let e := LinearEquiv.funUnique (Fin 1) ℂ V
  have hi (v : V) (j : Fin 1) : e (Pi.single j v) = v := by
    change (Pi.single j v : Fin 1 → V) default = v
    rw [show (default : Fin 1) = j from Subsingleton.elim _ _, Pi.single_eq_same]
  have hm (a : Fin 2 → Fin 1) :
      m1b_tensorEquiv e 2 (labeledInverseForm B hB hs 1 a) = inverseFormTensor B hB hs := by
    have hc : (m1b_tensorEquiv e 2).toLinearMap.comp (m1b_copyTensorIn 1 2 a) =
        (LinearMap.id : (⨂[ℂ]^2 V) →ₗ[ℂ] _) := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro v
      change m1b_tensorEquiv e 2 (m1b_copyTensorIn 1 2 a (PiTensorProduct.tprod ℂ v)) =
        PiTensorProduct.tprod ℂ v
      simp only [m1b_tensorEquiv, m1b_copyTensorIn, PiTensorProduct.map_tprod,
        PiTensorProduct.congr_tprod, LinearMap.single_apply, hi]
    exact LinearMap.congr_fun hc (inverseFormTensor B hB hs)
  have hf : (m1b_fixed (m1b_copies 1 '' m1b_isometries B) 2).map
      (m1b_tensorEquiv e 2).toLinearMap = m1b_fixed (m1b_isometries B) 2 := by
    rw [m1b_fixed_map, m1b_copies_one_conj]
  rw [← hf, orthogonal_quadratics_eq_inverseForm_span B hB hs 1,
    Submodule.map_span, ← Set.range_comp]
  simp only [Function.comp_def, LinearEquiv.coe_coe, hm, Set.range_const]

end HodgeLean.Foundations.Abdulali
