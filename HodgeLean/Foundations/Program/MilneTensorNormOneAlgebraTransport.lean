import HodgeLean.Foundations.Program.MilneTensorInvolutionTransport

noncomputable section
namespace HodgeLean.Foundations.Program
variable {R S : Type*} [Ring R] [Algebra ℂ R] [Ring S] [Algebra ℂ S]

theorem m1b_norm_one_algEquiv_image (e : R ≃ₐ[ℂ] S) (τ : R ≃ₗ[ℂ] R)
    (σ : S → S) (he : ∀ a, σ (e a) = e (τ a)) :
    e '' {a | τ a * a = 1} = {b | σ b * b = 1} := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    change σ (e a) * e a = 1
    rw [he, ← map_mul, ha, map_one]
  · intro hb
    refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    apply e.injective
    rw [map_mul, map_one, ← he, e.apply_symm_apply]
    exact hb

end HodgeLean.Foundations.Program
