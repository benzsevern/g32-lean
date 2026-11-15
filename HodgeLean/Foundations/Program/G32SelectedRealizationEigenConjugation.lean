import HodgeLean.Foundations.Program.G32SelectedRealizationEigenGenerator

noncomputable section
open HodgeLean.Foundations HodgeBlocks
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_cyclotomic_eigenspace_conjugation {V : Type*} [AddCommGroup V] [Module ℚ V]
    {m d : ℕ} (e : V ≃ₗ[ℚ] (Fin d → cyc_Field m))
    (σ τ : cyc_Field m →ₐ[ℚ] ℂ) (hτ : ∀ a, τ a = star (σ a)) :
    (cyc_eigenspace e σ).map (sigmaQ V) = cyc_eigenspace e τ := by
  have hc (σ τ : cyc_Field m →ₐ[ℚ] ℂ) (hτ : ∀ a, τ a = star (σ a))
      (v : ℂ ⊗[ℚ] V) (hv : v ∈ cyc_eigenspace e σ) :
      sigmaQ V v ∈ cyc_eigenspace e τ := by
    apply (Submodule.mem_iInf _).mpr
    intro a
    apply Module.End.mem_eigenspace_iff.mpr
    have he := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv a)
    rw [← sigmaQ_baseChange, he, map_smulₛₗ, hτ]
    rfl
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact hc σ τ hτ v hv
  · intro v hv
    refine ⟨sigmaQ V v, hc τ σ (fun a ↦ ?_) v hv, sigmaQ_involutive V v⟩
    rw [hτ, star_star]

end HodgeLean.Foundations.Program
