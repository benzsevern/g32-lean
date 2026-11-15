import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Rat

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

theorem g32c_baseChange_map_mem {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (f : V →ₗ[ℚ] W) (P : Submodule ℚ V)
    (Q : Submodule ℚ W) (hf : ∀ v ∈ P, f v ∈ Q)
    (x : ℂ ⊗[ℚ] V) (hx : x ∈ P.baseChange ℂ) :
    f.baseChange ℂ x ∈ Q.baseChange ℂ := by
  obtain ⟨z, rfl⟩ := hx
  induction z using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using (Submodule.zero_mem (Q.baseChange ℂ))
  | tmul a v =>
      simpa only [LinearMap.baseChange_tmul, Submodule.subtype_apply] using
        Submodule.tmul_mem_baseChange_of_mem a (hf v v.property)
  | add z w hz hw => simpa only [map_add] using Submodule.add_mem _ hz hw

theorem g32c_baseChange_bilinear_mem {V W T : Type*}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    [AddCommGroup T] [Module ℚ T]
    (F : ℂ ⊗[ℚ] V →ₗ[ℂ] ℂ ⊗[ℚ] W →ₗ[ℂ] ℂ ⊗[ℚ] T)
    (P : Submodule ℚ V) (Q : Submodule ℚ W) (R : Submodule ℚ T)
    (hf : ∀ a b v, v ∈ P → ∀ w, w ∈ Q →
      F (a ⊗ₜ v) (b ⊗ₜ w) ∈ R.baseChange ℂ)
    (x : ℂ ⊗[ℚ] V) (hx : x ∈ P.baseChange ℂ)
    (y : ℂ ⊗[ℚ] W) (hy : y ∈ Q.baseChange ℂ) : F x y ∈ R.baseChange ℂ := by
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simpa only [map_zero, LinearMap.zero_apply] using
      (Submodule.zero_mem (R.baseChange ℂ))
  | add z z' hz hz' =>
      simpa only [map_add, LinearMap.add_apply] using Submodule.add_mem _ hz hz'
  | tmul a v =>
      induction w using TensorProduct.induction_on with
      | zero => simpa only [map_zero] using (Submodule.zero_mem (R.baseChange ℂ))
      | add w w' hw hw' => simpa only [map_add] using Submodule.add_mem _ hw hw'
      | tmul b t =>
          simpa only [LinearMap.baseChange_tmul, Submodule.subtype_apply] using hf a b v v.property t t.property

end HodgeLean.Foundations.Program
