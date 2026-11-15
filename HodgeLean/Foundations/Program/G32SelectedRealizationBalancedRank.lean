import HodgeLean.Foundations.Program.G32SelectedRealizationEigenDimension
import HodgeLean.Foundations.Program.G32SelectedRealizationEigenConjugation
import HodgeLean.Foundations.Program.G32SelectedRealizationEigenSplit

noncomputable section
open HodgeLean.Foundations HodgeBlocks
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_cyclotomic_balanced_rank {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {m d k : ℕ} (hm : 3 ≤ m) (hd : 0 < d)
    (e : V ≃ₗ[ℚ] (Fin d → cyc_Field m))
    (H₀ H₁ : Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : H₀ ⊔ H₁ = ⊤)
    (hdis : Disjoint H₀ H₁) (hswap : H₀.map (sigmaQ V) = H₁)
    (hp : ∀ a (i : Bool), (if i then H₀ else H₁).map ((cyc_scalar e a).baseChange ℂ) ≤
      if i then H₀ else H₁)
    (σ τ : cyc_Field m →ₐ[ℚ] ℂ) (hτ : ∀ a, τ a = star (σ a))
    (hsig : ∀ ρ : cyc_Field m →ₐ[ℚ] ℂ,
      Module.finrank ℂ ↥(cyc_eigenspace e ρ ⊓ H₀) = k) : d = 2 * k := by
  letI : NeZero m := ⟨by omega⟩
  have hinj : Function.Injective (sigmaQ V) := by
    intro x y h
    simpa only [sigmaQ_involutive] using congrArg (sigmaQ V) h
  have hc : (cyc_eigenspace e τ).map (sigmaQ V) = cyc_eigenspace e σ :=
    g32y_cyclotomic_eigenspace_conjugation e τ σ (fun a ↦ by rw [hτ, star_star])
  have h₁ : Module.finrank ℂ ↥(cyc_eigenspace e σ ⊓ H₁) = k := by
    have hh := WeilAction.finrank_map_sigmaQ (cyc_eigenspace e τ ⊓ H₀)
    rw [Submodule.map_inf _ hinj, hc, hswap] at hh
    exact hh.trans (hsig τ)
  let A := (cyc_scalar e (IsCyclotomicExtension.zeta m ℚ (cyc_Field m))).baseChange ℂ
  have hsplit : cyc_eigenspace e σ =
      (cyc_eigenspace e σ ⊓ H₀) ⊔ (cyc_eigenspace e σ ⊓ H₁) := by
    rw [g32y_cyclotomic_eigenspace_generator]
    apply g32y_eigenspace_split A H₀ H₁ hH hdis
    · intro x hx
      exact hp _ true ⟨x, hx, rfl⟩
    · intro x hx
      exact hp _ false ⟨x, hx, rfl⟩
  have hdim := g32y_cyclotomic_eigenspace_dimension e σ
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (cyc_eigenspace e σ ⊓ H₀) (cyc_eigenspace e σ ⊓ H₁)
  have hdi : Disjoint (cyc_eigenspace e σ ⊓ H₀) (cyc_eigenspace e σ ⊓ H₁) :=
    hdis.mono inf_le_right inf_le_right
  rw [hdi.eq_bot, finrank_bot, add_zero, ← hsplit, hdim, hsig σ, h₁] at hsum
  omega

end HodgeLean.Foundations.Program
