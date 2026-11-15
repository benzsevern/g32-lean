import HodgeLean.Foundations.Program.G32Native.CanonicalAbelKernelLinearAlgebra

/-! # The transpose line from a tangent inclusion and a line bound -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.G32Native

/-- A transpose kernel contained in a line fills that line when the original tangent has half dimension. -/
theorem linear_transpose_kernel_eq_line_of_le (k : ℕ)
    (A : (Fin (k + k) → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin (k + 1) → ℂ))
    (i : (Fin k → ℂ) →ₗ[ℂ] (Fin (k + k) → ℂ)) (hi : Function.Injective i)
    (hvan : ∀ v, A (i v) = 0)
    (L : Projectivization ℂ (Fin (k + 1) → ℂ))
    (hle : LinearMap.ker (A.dualMap.comp (Module.Dual.eval ℂ (Fin (k + 1) → ℂ))) ≤
      L.submodule) :
    LinearMap.ker (A.dualMap.comp (Module.Dual.eval ℂ (Fin (k + 1) → ℂ))) = L.submodule := by
  let T := A.dualMap.comp (Module.Dual.eval ℂ (Fin (k + 1) → ℂ))
  have hrange : LinearMap.range T = LinearMap.range A.dualMap := by
    apply LinearMap.range_comp_of_range_eq_top
    exact (Module.evalEquiv ℂ (Fin (k + 1) → ℂ)).range
  have hrt := T.finrank_range_add_finrank_ker
  rw [hrange, LinearMap.finrank_range_dualMap_eq_finrank_range, Module.finrank_fin_fun] at hrt
  have hka := A.finrank_range_add_finrank_ker
  rw [Module.finrank_fin_fun] at hka
  have hki : Module.finrank ℂ (LinearMap.range i) = k := by
    rw [LinearMap.finrank_range_of_inj hi, Module.finrank_fin_fun]
  have hle' : LinearMap.range i ≤ LinearMap.ker A := by
    rintro _ ⟨v, rfl⟩
    exact hvan v
  have hdim := Submodule.finrank_mono hle'
  have hdimT := Submodule.finrank_mono hle
  rw [L.finrank_submodule] at hdimT
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [L.finrank_submodule]
  change Module.finrank ℂ (LinearMap.ker T) = 1
  dsimp only [T] at *
  omega

#print axioms linear_transpose_kernel_eq_line_of_le
end HodgeLean.Foundations.Program.G32Native
