import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Scalar extension through the dual of a finite rational vector space
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.AnalyticAlbanese.ConsumerBridge

/-- Extending a rational dual equivalence gives a bijection onto the complex tensor dual.
HC no distance; AV milestone no distance. -/
theorem dualScalarExtension_bijective {V W : Type} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] [Module.Finite ℚ V]
    (e : W ≃ₗ[ℚ] Module.Dual ℚ V) :
    Function.Bijective (LinearMap.liftBaseChange ℂ (Module.Dual.baseChange ℂ ∘ₗ e.toLinearMap)) := by
  let B := TensorProduct.isBaseChange ℚ V ℂ
  have he : LinearMap.liftBaseChange ℂ (Module.Dual.baseChange ℂ ∘ₗ e.toLinearMap) =
      B.toDualBaseChange.toLinearMap.comp (e.baseChange ℚ ℂ _ _).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a c
    apply B.algHom_ext
    intro v
    simp only [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply,
      LinearEquiv.coe_baseChange, LinearMap.baseChange_tmul, LinearMap.smul_apply,
      Module.Dual.baseChange_apply_tmul]
    exact (congrArg (fun z : ℂ => a • z)
      (Module.Dual.baseChange_apply_tmul ℂ (e c) 1 v)).trans
        (by simpa [Algebra.smul_def, smul_eq_mul] using
          (B.toDualBaseChange_tmul a (e c) v).symm)
  rw [he]
  exact B.toDualBaseChange.bijective.comp (e.baseChange ℚ ℂ _ _).bijective

end HodgeLean.Foundations.AnalyticAlbanese.ConsumerBridge
