import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Rat

/-! Injectivity of scalar extension into the full dual without a dimension restriction. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_tensor_dual_injective
    (V : Type) [AddCommGroup V] [Module ℚ V] :
    Function.Injective (LinearMap.liftBaseChange ℂ (Module.Dual.baseChange ℂ (R := ℚ) (V := V))) := by
  classical
  let b := Module.Free.chooseBasis ℚ ℂ
  let F := LinearMap.liftBaseChange ℂ (Module.Dual.baseChange ℂ (R := ℚ) (V := V))
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := Module.Dual ℚ V) b
  have hcoord (x : ℂ ⊗[ℚ] Module.Dual ℚ V) (i : Module.Free.ChooseBasisIndex ℚ ℂ)
      (v : V) : E x i v = b.coord i (F x ((1 : ℂ) ⊗ₜ[ℚ] v)) := by
    induction x using TensorProduct.inductionOn with
    | tmul a f =>
      simp only [E, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
        LinearMap.smul_apply, smul_eq_mul, F, LinearMap.liftBaseChange_tmul,
        LinearMap.smul_apply, Module.Dual.baseChange_apply_tmul]
      change b.repr a i * f v = b.coord i (a * ((f v) • (1 : ℂ)))
      rw [show a * ((f v) • (1 : ℂ)) = (f v) • a by
        simp only [Algebra.smul_def, one_mul, mul_comm]]
      rw [map_smul]
      exact mul_comm _ _
    | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, LinearMap.add_apply, hx, hy]
  intro x y hxy
  apply E.injective
  ext i v
  rw [hcoord, hcoord, hxy]

end HodgeLean.Foundations.QuotientDuality
