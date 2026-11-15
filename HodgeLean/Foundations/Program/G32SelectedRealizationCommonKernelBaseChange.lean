import HodgeLean.Foundations.Program.G32SelectedRealizationKernelBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_baseChange_common_kernel {I U V : Type*} [Fintype I]
    [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    (A : I → U →ₗ[ℚ] V) :
    LinearMap.range ((⨅ i, LinearMap.ker (A i)).subtype.baseChange ℂ) =
      ⨅ i, LinearMap.ker ((A i).baseChange ℂ) := by
  classical
  let f := LinearMap.pi A
  let e := TensorProduct.piRight ℚ ℂ ℂ (fun _ : I ↦ V)
  have hc : e.toLinearMap ∘ₗ f.baseChange ℂ =
      LinearMap.pi (fun i ↦ (A i).baseChange ℂ) := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul c u => ext i; rfl
    | add x y hx hy => simp only [map_add, LinearMap.comp_apply, hx, hy]
  have hk : LinearMap.ker (f.baseChange ℂ) =
      ⨅ i, LinearMap.ker ((A i).baseChange ℂ) := by
    rw [← LinearMap.ker_comp_of_ker_eq_bot (f.baseChange ℂ) e.ker, hc,
      LinearMap.ker_pi]
  have hh := g32y_baseChange_kernel f
  rw [hk] at hh
  change LinearMap.range ((LinearMap.ker (LinearMap.pi A)).subtype.baseChange ℂ) = _ at hh
  rw [LinearMap.ker_pi A] at hh
  exact hh

end HodgeLean.Foundations.Program
