import HodgeLean.Foundations.Program.MilneTensorInvolutionCoordinates

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} [DecidableEq ι] (A : ι → Type*)
    [∀ i, Ring (A i)] [∀ i, Algebra ℂ (A i)]

theorem m1b_involution_piId
    (τ : ((i : ι) → A i) ≃ₗ[ℂ] ((i : ι) → A i))
    (hmul : ∀ a b, τ (a * b) = τ b * τ a) (σ : Equiv.Perm ι)
    (hσ : ∀ i, τ (Pi.single i 1) = Pi.single (σ i) 1)
    (p : ι → Prop) [DecidablePred p] (hp : ∀ i, p (σ i) ↔ p i) :
    τ (m1b_piId A p) = m1b_piId A p := by
  funext j
  obtain ⟨i, rfl⟩ := σ.surjective j
  rw [m1b_involution_coordinate A τ hmul σ hσ]
  by_cases h : p i
  · have h' : p (σ i) := (hp i).mpr h
    simp only [m1b_piId, if_pos h, if_pos h', hσ i, Pi.single_eq_same]
  · have h' : ¬p (σ i) := fun hi => h ((hp i).mp hi)
    simp only [m1b_piId, if_neg h, if_neg h', Pi.single_zero, map_zero, Pi.zero_apply]

end HodgeLean.Foundations.Program
