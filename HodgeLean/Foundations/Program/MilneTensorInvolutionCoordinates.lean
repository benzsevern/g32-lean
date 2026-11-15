import HodgeLean.Foundations.Program.MilneTensorPiSplit

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [DecidableEq ι] (A : ι → Type*)
    [∀ i, Ring (A i)] [∀ i, Algebra ℂ (A i)]

theorem m1b_involution_coordinate
    (τ : ((i : ι) → A i) ≃ₗ[ℂ] ((i : ι) → A i))
    (hmul : ∀ a b, τ (a * b) = τ b * τ a) (σ : Equiv.Perm ι)
    (hσ : ∀ i, τ (Pi.single i 1) = Pi.single (σ i) 1)
    (X : (i : ι) → A i) (i : ι) :
    τ X (σ i) = τ (Pi.single i (X i)) (σ i) := by
  have hprod : Pi.single i (1 : A i) * X = Pi.single i (X i) := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [Pi.mul_apply, Pi.single_eq_same, one_mul]
    · simp only [Pi.mul_apply, Pi.single_eq_of_ne h, zero_mul]
  have h := congrFun (hmul (Pi.single i 1) X) (σ i)
  rw [hprod, hσ i] at h
  simpa only [Pi.mul_apply, Pi.single_eq_same, mul_one] using h.symm

end HodgeLean.Foundations.Program
