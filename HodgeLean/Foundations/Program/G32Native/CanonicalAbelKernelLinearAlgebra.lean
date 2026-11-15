import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # From a transpose form line to the exact immersion tangent kernel -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.G32Native

/-- A one-dimensional transpose kernel and the retained tangent inclusion give the exact kernel. -/
theorem linear_kernel_eq_range_of_transpose_line (k : ℕ)
    (A : (Fin (k + k) → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin (k + 1) → ℂ))
    (i : (Fin k → ℂ) →ₗ[ℂ] (Fin (k + k) → ℂ)) (hi : Function.Injective i)
    (hvan : ∀ v, A (i v) = 0)
    (L : Projectivization ℂ (Fin (k + 1) → ℂ))
    (hker : LinearMap.ker (A.dualMap.comp (Module.Dual.eval ℂ (Fin (k + 1) → ℂ))) =
      L.submodule) :
    LinearMap.ker A = LinearMap.range i ∧ ∀ v, A v L.rep = 0 := by
  let T := A.dualMap.comp (Module.Dual.eval ℂ (Fin (k + 1) → ℂ))
  have hrange : LinearMap.range T = LinearMap.range A.dualMap := by
    apply LinearMap.range_comp_of_range_eq_top
    exact (Module.evalEquiv ℂ (Fin (k + 1) → ℂ)).range
  have hrt := T.finrank_range_add_finrank_ker
  rw [hrange, LinearMap.finrank_range_dualMap_eq_finrank_range,
    hker, L.finrank_submodule, Module.finrank_fin_fun] at hrt
  have hra : Module.finrank ℂ (LinearMap.range A) = k := by omega
  have hka := A.finrank_range_add_finrank_ker
  rw [hra, Module.finrank_fin_fun] at hka
  have hki : Module.finrank ℂ (LinearMap.range i) = k := by
    rw [LinearMap.finrank_range_of_inj hi, Module.finrank_fin_fun]
  have hle : LinearMap.range i ≤ LinearMap.ker A := by
    rintro _ ⟨v, rfl⟩
    exact hvan v
  constructor
  · exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  · intro v
    have hrep : L.rep ∈ LinearMap.ker T := by
      rw [hker, L.submodule_eq]
      exact Submodule.subset_span (Set.mem_singleton _)
    have he : T L.rep = 0 := hrep
    exact congrArg (fun f : Module.Dual ℂ (Fin (k + k) → ℂ) => f v) he

#print axioms linear_kernel_eq_range_of_transpose_line
end HodgeLean.Foundations.Program.G32Native
