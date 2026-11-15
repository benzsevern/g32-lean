import HodgeLean.Foundations.RepFoundationsSymplectic

/-! # Proof obligations for the representation foundations specification -/

noncomputable section

namespace HodgeLean.Foundations

open CategoryTheory
open scoped TensorProduct

variable {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

theorem rfd_eval_bijective_aux {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i)) :
    Function.Bijective (rfd_eval σ ρ) :=
  rfd_eval_bijective' σ ρ hσ hdist hcov

theorem rfd_det_eq_prod_aux {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i))
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) :
    LinearMap.det u = ∏ i, rfd_det (σ i) ρ u hu ^ Module.finrank ℂ (σ i) :=
  rfd_det_eq_prod' σ ρ hσ hdist hcov u hu

theorem rfd_det_eigen_aux {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G)
    (ρ : Representation ℂ G V) (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i))
    (H : Subgroup G) (χ : H →* ℂˣ)
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) :
    LinearMap.det (rfd_eigenAct ρ H χ u hu) =
      ∏ i, rfd_det (σ i) ρ u hu ^ Module.finrank ℂ (rfd_eigen (σ i).ρ H χ) :=
  rfd_det_eigen' σ ρ hσ hdist hcov H χ u hu

theorem rfd_indicator_trichotomy_aux (σ : FDRep ℂ G) (hσ : Simple σ) :
    (rfd_indicator σ = 1 ∨ rfd_indicator σ = 0 ∨ rfd_indicator σ = -1) ∧
      (rfd_indicator σ = 0 ↔ ¬ ∀ g, star (σ.character g) = σ.character g) :=
  ⟨(rfd_indicator_cases σ hσ).1, (rfd_indicator_cases σ hσ).2.1⟩

theorem rfd_indicator_forms_aux (σ : FDRep ℂ G) (hσ : Simple σ) :
    (rfd_indicator σ = 1 ↔ ∃ B ∈ rfd_invForms σ, B ≠ 0 ∧ B.IsSymm) ∧
    (rfd_indicator σ = -1 ↔ ∃ B ∈ rfd_invForms σ, B ≠ 0 ∧ B.IsAlt) ∧
    (rfd_indicator σ = 0 ↔ rfd_invForms σ = ⊥) :=
  (rfd_indicator_cases σ hσ).2.2

theorem rfd_det_mul_dual_aux (ρ : Representation ℂ G V) (ω : LinearMap.BilinForm ℂ V)
    (hω : ω.Nondegenerate) (hωG : ∀ g x y, ω (ρ g x) (ρ g y) = ω x y)
    (σ σbar : FDRep ℂ G) (hσ : Simple σ)
    (hchar : ∀ g, σbar.character g = star (σ.character g))
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ))
    (huω : ∀ x y, ω (u x) (u y) = ω x y) :
    rfd_det σbar ρ u hu * rfd_det σ ρ u hu = 1 :=
  rfd_det_mul_dual' ρ ω hω hωG σ σbar hσ hchar u hu huω

theorem rfd_det_orthogonal_aux (ρ : Representation ℂ G V) (ω : LinearMap.BilinForm ℂ V)
    (hω : ω.Nondegenerate) (hωalt : ω.IsAlt) (hωG : ∀ g x y, ω (ρ g x) (ρ g y) = ω x y)
    (σ : FDRep ℂ G) (hσ : Simple σ) (hν : rfd_indicator σ = 1)
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ))
    (huω : ∀ x y, ω (u x) (u y) = ω x y) :
    rfd_det σ ρ u hu = 1 :=
  rfd_det_orthogonal' ρ ω hω hωalt hωG σ hσ hν u hu huω

theorem rfd_mult_eq_bot_aux (σ : FDRep ℂ G) (ρ : Representation ℂ G V) (n : ℤ)
    (hn : (Fintype.card G : ℂ)⁻¹ *
      ∑ g, LinearMap.trace ℂ V (ρ g) * star (σ.character g) = n)
    (hle : n ≤ 0) :
    rfd_mult σ ρ = ⊥ := by
  have hk : (Module.finrank ℂ (rfd_mult σ ρ) : ℂ) = n := by
    rw [(rfd_multEquiv σ ρ).finrank_eq, rfd_finrank_intertwiningMap, ← hn]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [rfd_star_character]
    rfl
  have hk' : (Module.finrank ℂ (rfd_mult σ ρ) : ℤ) = n := by exact_mod_cast hk
  exact Submodule.finrank_eq_zero.1 (by omega)

end HodgeLean.Foundations
