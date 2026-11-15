import HodgeLean.Foundations.Program.MilneTensorDefs
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem m1b_right_coeff_map {ι : Type*} [DecidableEq ι] (b : Module.Basis ι ℂ W)
    (u : Module.End ℂ V) (t : V ⊗[ℂ] W) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight b (TensorProduct.map u LinearMap.id t) i =
      u (TensorProduct.equivFinsuppOfBasisRight b t i) := by
  classical
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp_all

theorem m1b_fixed_left_lift (S : Set (Module.End ℂ V))
    (t : V ⊗[ℂ] W) (ht : ∀ u ∈ S, TensorProduct.map u LinearMap.id t = t) :
    ∃ z : ↥(⨅ u ∈ S, LinearMap.ker (u - LinearMap.id)) ⊗[ℂ] W,
      TensorProduct.map (⨅ u ∈ S, LinearMap.ker (u - LinearMap.id)).subtype
        LinearMap.id z = t := by
  classical
  let P : Submodule ℂ V := ⨅ u ∈ S, LinearMap.ker (u - LinearMap.id)
  let b := Module.Free.chooseBasis ℂ W
  let c := TensorProduct.equivFinsuppOfBasisRight b t
  have hc (i) : c i ∈ P := by
    simp only [P, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro u hu
    change u (TensorProduct.equivFinsuppOfBasisRight b t i) = _
    rw [← m1b_right_coeff_map, ht u hu]
  refine ⟨∑ i ∈ c.support, (⟨c i, hc i⟩ : P) ⊗ₜ[ℂ] b i, ?_⟩
  simp only [map_sum, TensorProduct.map_tmul, Submodule.subtype_apply, LinearMap.id_apply]
  simpa only [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum] using
    (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply t

theorem m1b_left_coeff_map {ι : Type*} [DecidableEq ι] (b : Module.Basis ι ℂ V)
    (v : Module.End ℂ W) (t : V ⊗[ℂ] W) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (TensorProduct.map LinearMap.id v t) i =
      v (TensorProduct.equivFinsuppOfBasisLeft b t i) := by
  classical
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp_all

end HodgeLean.Foundations.Program
