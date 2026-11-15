import HodgeLean.Foundations.Program.MilneTensorHelpers

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_products_mono (Q R : Submodule ℂ (⨂[ℂ]^2 V)) (h : Q ≤ R) :
    ∀ n, m1b_products Q n ≤ m1b_products R n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact le_rfl
  | one => exact le_rfl
  | more n ih _ =>
    apply Submodule.span_mono
    rintro t ⟨σ, a, b, ha, hb, rfl⟩
    exact ⟨σ, a, b, ih ha, h hb, rfl⟩

end HodgeLean.Foundations.Program
