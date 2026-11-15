import HodgeLean.Foundations.Program.MilneTensorFamilyMaps

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem m1b_products_map_family
    (Q : Submodule ℂ (⨂[ℂ]^2 V)) (R : Submodule ℂ (⨂[ℂ]^2 W))
    (F : Set (V →ₗ[ℂ] W))
    (hquad : ∀ (g : Fin 2 → V →ₗ[ℂ] W), (∀ i, g i ∈ F) →
      ∀ b ∈ Q, PiTensorProduct.map g b ∈ R) :
    ∀ (n : ℕ) (f : Fin n → V →ₗ[ℂ] W), (∀ i, f i ∈ F) →
      ∀ t ∈ m1b_products Q n, PiTensorProduct.map f t ∈ m1b_products R n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro f hf t ht; exact Submodule.mem_top
  | one =>
    intro f hf t ht
    have hz : t = 0 := ht
    rw [hz, map_zero]
    exact Submodule.zero_mem _
  | more n ih _ =>
    intro f hf t ht
    rw [m1b_products] at ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨σ, a, b, ha, hb, rfl⟩ := ht
      rw [m1b_tensorMap_perm, m1b_tensorMap_append]
      apply Submodule.subset_span
      exact ⟨σ, _, _, ih _ (fun i => hf _) a ha,
        hquad _ (fun i => hf _) b hb, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul c x hx ihx => rw [map_smul]; exact Submodule.smul_mem _ c ihx

end HodgeLean.Foundations.Program
