import HodgeLean.Foundations.Program.MilneTensorInvolutionProduct

noncomputable section
namespace HodgeLean.Foundations.Program
variable {R S : Type*} [Ring R] [Algebra ℂ R] [Ring S] [Algebra ℂ S]

theorem m1b_involution_prod_split (τ : (R × S) ≃ₗ[ℂ] (R × S))
    (hτ : Function.Involutive τ) (hmul : ∀ a b, τ (a * b) = τ b * τ a)
    (hleft : τ (1, 0) = (1, 0)) :
    ∃ (α : R ≃ₗ[ℂ] R) (β : S ≃ₗ[ℂ] S),
      Function.Involutive α ∧ Function.Involutive β ∧
      (∀ a b, α (a * b) = α b * α a) ∧
      (∀ a b, β (a * b) = β b * β a) ∧
      ∀ z, τ z = (α z.1, β z.2) := by
  obtain ⟨hzl, hzr⟩ := m1b_involution_prod_components τ hmul hleft
  let f : R →ₗ[ℂ] R := (LinearMap.fst ℂ R S).comp
    (τ.toLinearMap.comp (LinearMap.inl ℂ R S))
  let g : S →ₗ[ℂ] S := (LinearMap.snd ℂ R S).comp
    (τ.toLinearMap.comp (LinearMap.inr ℂ R S))
  have hl (r : R) : τ (r, 0) = (f r, 0) := Prod.ext rfl (hzl r)
  have hr (s : S) : τ (0, s) = (0, g s) := Prod.ext (hzr s) rfl
  have hf (r : R) : f (f r) = r := by
    have h := hτ (r, 0)
    rw [hl, hl] at h
    exact congrArg Prod.fst h
  have hg (s : S) : g (g s) = s := by
    have h := hτ (0, s)
    rw [hr, hr] at h
    exact congrArg Prod.snd h
  let α : R ≃ₗ[ℂ] R :=
    { toLinearMap := f, invFun := f, left_inv := hf, right_inv := hf }
  let β : S ≃ₗ[ℂ] S :=
    { toLinearMap := g, invFun := g, left_inv := hg, right_inv := hg }
  refine ⟨α, β, hf, hg, ?_, ?_, ?_⟩
  · intro a b
    change (τ (a * b, 0)).1 = (τ (b, 0)).1 * (τ (a, 0)).1
    have h := congrArg Prod.fst (hmul (a, 0) (b, 0))
    simpa only [Prod.mk_mul_mk, mul_zero, Prod.fst_mul] using h
  · intro a b
    change (τ (0, a * b)).2 = (τ (0, b)).2 * (τ (0, a)).2
    have h := congrArg Prod.snd (hmul (0, a) (0, b))
    simpa only [Prod.mk_mul_mk, mul_zero, Prod.snd_mul] using h
  · intro z
    have h : z = (z.1, 0) + (0, z.2) := by ext <;> simp
    rw [h, map_add, hl, hr]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    rfl

end HodgeLean.Foundations.Program
