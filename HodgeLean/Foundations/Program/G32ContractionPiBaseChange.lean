import HodgeLean.Foundations.Program.G32ContractionScalar
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Module.Submodule.Equiv

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

theorem g32c_baseChange_bijective {V W : Type*}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (f : V →ₗ[ℚ] W) (hf : Function.Bijective f) : Function.Bijective (f.baseChange ℂ) := by
  let e := LinearEquiv.ofBijective f hf
  change Function.Bijective ((e.baseChange ℚ ℂ V W).toLinearMap)
  exact (e.baseChange ℚ ℂ V W).bijective

theorem g32c_piSum_baseChange {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    {W : Type*} [AddCommGroup W] [Module ℚ W] (f : ∀ i, V i →ₗ[ℚ] W) :
    (∑ i, (f i).baseChange ℂ ∘ₗ LinearMap.proj i) ∘ₗ
      (TensorProduct.piRight ℚ ℂ ℂ V).toLinearMap =
      (∑ i, f i ∘ₗ LinearMap.proj i).baseChange ℂ := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.baseChange_tmul, TensorProduct.tmul_sum]

theorem g32c_piSum_baseChange_bijective {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    {W : Type*} [AddCommGroup W] [Module ℚ W] (f : ∀ i, V i →ₗ[ℚ] W)
    (hf : Function.Bijective (∑ i, f i ∘ₗ LinearMap.proj i : (∀ i, V i) →ₗ[ℚ] W)) :
    Function.Bijective (∑ i, (f i).baseChange ℂ ∘ₗ LinearMap.proj i :
      (∀ i, ℂ ⊗[ℚ] V i) →ₗ[ℂ] ℂ ⊗[ℚ] W) := by
  have h := g32c_baseChange_bijective (∑ i, f i ∘ₗ LinearMap.proj i) hf
  rw [← g32c_piSum_baseChange f] at h
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := (TensorProduct.piRight ℚ ℂ ℂ V).surjective x
    obtain ⟨b, rfl⟩ := (TensorProduct.piRight ℚ ℂ ℂ V).surjective y
    apply congrArg (TensorProduct.piRight ℚ ℂ ℂ V)
    apply h.1
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using hxy
  · intro z
    obtain ⟨w, hw⟩ := h.2 z
    refine ⟨TensorProduct.piRight ℚ ℂ ℂ V w, ?_⟩
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using hw

end HodgeLean.Foundations.Program
