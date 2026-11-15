import HodgeLean.Foundations.Program.G32SelectedRealizationEigenConjugation

noncomputable section
open HodgeBlocks
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_rational_comap_conjugation {V W : Type*}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (j : V →ₗ[ℚ] W) (H₀ H₁ : Submodule ℂ (ℂ ⊗[ℚ] W))
    (hH : H₀.map (sigmaQ W) = H₁) :
    (H₀.comap (j.baseChange ℂ)).map (sigmaQ V) = H₁.comap (j.baseChange ℂ) := by
  have hc (x : ℂ ⊗[ℚ] V) :
      sigmaQ W (j.baseChange ℂ x) = j.baseChange ℂ (sigmaQ V x) :=
    sigmaQ_baseChange j x
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    change j.baseChange ℂ (sigmaQ V v) ∈ H₁
    rw [← hc, ← hH]
    exact ⟨j.baseChange ℂ v, hv, rfl⟩
  · intro v hv
    refine ⟨sigmaQ V v, ?_, sigmaQ_involutive V v⟩
    change j.baseChange ℂ (sigmaQ V v) ∈ H₀
    rw [← hc]
    change j.baseChange ℂ v ∈ H₁ at hv
    rw [← hH] at hv
    obtain ⟨z, hz, he⟩ := hv
    rw [← he, sigmaQ_involutive]
    exact hz

end HodgeLean.Foundations.Program
