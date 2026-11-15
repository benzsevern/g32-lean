import HodgeLean.Foundations.Program.MilneTensorPiSplit
import HodgeLean.Foundations.Program.MilneTensorInvolutionSplit
import HodgeLean.Foundations.Program.MilneTensorInvolutionTransport

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} (A : ι → Type*) [∀ i, Ring (A i)] [∀ i, Algebra ℂ (A i)]

theorem m1b_pi_involution_split (p : ι → Prop) [DecidablePred p]
    (τ : ((i : ι) → A i) ≃ₗ[ℂ] ((i : ι) → A i))
    (hτ : Function.Involutive τ) (hmul : ∀ a b, τ (a * b) = τ b * τ a)
    (hid : τ (m1b_piId A p) = m1b_piId A p) :
    ∃ (α : ((i : {i // p i}) → A i.val) ≃ₗ[ℂ] ((i : {i // p i}) → A i.val))
      (β : ((i : {i // ¬p i}) → A i.val) ≃ₗ[ℂ] ((i : {i // ¬p i}) → A i.val)),
      Function.Involutive α ∧ Function.Involutive β ∧
      (∀ a b, α (a * b) = α b * α a) ∧
      (∀ a b, β (a * b) = β b * β a) ∧
      ∀ X, m1b_piSplitAlgEquiv A p (τ X) =
        (α (m1b_piSplitAlgEquiv A p X).1, β (m1b_piSplitAlgEquiv A p X).2) := by
  let e := m1b_piSplitAlgEquiv A p
  let θ := m1b_transportInvolution e τ
  obtain ⟨hθ, hθmul⟩ := m1b_transportInvolution_properties e τ hτ hmul
  have hleft : θ (1, 0) = (1, 0) := by
    change e (τ (e.symm (1, 0))) = (1, 0)
    have heq : e (m1b_piId A p) = (1, 0) := m1b_piSplit_left_id A p
    rw [← heq, e.symm_apply_apply, hid]
  obtain ⟨α, β, hα, hβ, hαmul, hβmul, hparts⟩ :=
    m1b_involution_prod_split θ hθ hθmul hleft
  refine ⟨α, β, hα, hβ, hαmul, hβmul, ?_⟩
  intro X
  have h := hparts (e X)
  change e (τ (e.symm (e X))) = (α (e X).1, β (e X).2) at h
  rw [e.symm_apply_apply] at h
  exact h

end HodgeLean.Foundations.Program
