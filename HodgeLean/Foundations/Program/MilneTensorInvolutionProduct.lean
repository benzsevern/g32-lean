import HodgeLean.Foundations.Program.MilneTensorNormOneTransport

noncomputable section
namespace HodgeLean.Foundations.Program

variable {R S : Type*} [Ring R] [Algebra ℂ R] [Ring S] [Algebra ℂ S]

theorem m1b_involution_prod_components (τ : (R × S) ≃ₗ[ℂ] (R × S))
    (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hleft : τ (1, 0) = (1, 0)) :
    (∀ r : R, (τ (r, 0)).2 = 0) ∧ (∀ s : S, (τ (0, s)).1 = 0) := by
  have hright : τ (0, 1) = (0, 1) := by
    have h : ((0, 1) : R × S) = 1 - (1, 0) := by ext <;> simp
    rw [h, map_sub, m1b_involution_one τ hmul, hleft]
  constructor
  · intro r
    have h := congrArg Prod.snd (hmul (r, 0) (1, 0))
    simpa only [Prod.mk_mul_mk, mul_one, mul_zero, hleft, Prod.snd_mul, zero_mul] using h
  · intro s
    have h := congrArg Prod.fst (hmul (0, s) (0, 1))
    simpa only [Prod.mk_mul_mk, mul_one, mul_zero, hright, Prod.fst_mul, zero_mul] using h

end HodgeLean.Foundations.Program
