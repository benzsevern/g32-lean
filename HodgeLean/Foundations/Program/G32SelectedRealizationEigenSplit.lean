import HodgeLean.Foundations.Program.G32SelectedRealizationEigenImage

noncomputable section
namespace HodgeLean.Foundations.Program

theorem g32y_eigenspace_split {K U : Type*} [Field K] [AddCommGroup U] [Module K U]
    (A : Module.End K U) (H₀ H₁ : Submodule K U)
    (hH : H₀ ⊔ H₁ = ⊤) (hd : Disjoint H₀ H₁)
    (h₀ : ∀ x ∈ H₀, A x ∈ H₀) (h₁ : ∀ x ∈ H₁, A x ∈ H₁) (μ : K) :
    Module.End.eigenspace A μ =
      (Module.End.eigenspace A μ ⊓ H₀) ⊔ (Module.End.eigenspace A μ ⊓ H₁) := by
  apply le_antisymm
  · intro x hx
    have hxH : x ∈ H₀ ⊔ H₁ := by rw [hH]; trivial
    obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Submodule.mem_sup.mp hxH
    have he := Module.End.mem_eigenspace_iff.mp hx
    have hz : (A x₀ - μ • x₀) + (A x₁ - μ • x₁) = 0 := by
      rw [map_add, smul_add] at he
      calc
        _ = (A x₀ + A x₁) - (μ • x₀ + μ • x₁) := by abel
        _ = 0 := sub_eq_zero.mpr he
    have hmem₀ : A x₀ - μ • x₀ ∈ H₀ := H₀.sub_mem (h₀ _ hx₀) (H₀.smul_mem _ hx₀)
    have hmem₁ : A x₁ - μ • x₁ ∈ H₁ := H₁.sub_mem (h₁ _ hx₁) (H₁.smul_mem _ hx₁)
    have hz₀ : A x₀ - μ • x₀ = 0 := by
      have hh : A x₀ - μ • x₀ ∈ H₁ := by
        rw [eq_neg_of_add_eq_zero_left hz]
        exact H₁.neg_mem hmem₁
      exact hd.le_bot ⟨hmem₀, hh⟩
    have hz₁ : A x₁ - μ • x₁ = 0 := by simpa only [hz₀, zero_add] using hz
    exact Submodule.add_mem _
      (Submodule.mem_sup_left ⟨Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp hz₀), hx₀⟩)
      (Submodule.mem_sup_right ⟨Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp hz₁), hx₁⟩)
  · exact sup_le inf_le_left inf_le_left

end HodgeLean.Foundations.Program
