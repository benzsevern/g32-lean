import HodgeLean.Foundations.Program.PrymParabolicSaturatedComparison

/-! # Proofs for stage H5, first part: the saturated cellular lattice

The `_aux` theorems that `PrymParabolicSaturated.lean` restates. Their bodies cite the lemma
files `PrymParabolicSaturatedLemmas`, `PrymParabolicSaturatedSchur` and
`PrymParabolicSaturatedComparison`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open HodgeLean.Papers
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

theorem hg6_cellLattice_basis_aux :
    Nonempty (Module.Basis (Fin 12) ℤ hg6_cellLattice) :=
  hg6_cellLattice_basis_lemma

theorem hg6_cellOperator_sq_aux (x : hg6_cellLattice) :
    hg6_cellOperator (hg6_cellOperator x) = (-3 : ℤ) • x :=
  hg6_cellOperator_sq_lemma x

theorem hg6_saturated_transport_aux {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N]
    (ρ : b4b_Group → M →ₗ[ℤ] M) (ρ' : b4b_Group → N →ₗ[ℤ] N) (e : M ≃ₗ[ℤ] N)
    (he : ∀ h x, e (ρ h x) = ρ' h (e x)) :
    (b63l_saturation (LinearMap.range (hg6_projOf ρ))).map (e : M →ₗ[ℤ] N) =
        b63l_saturation (LinearMap.range (hg6_projOf ρ')) ∧
      ∀ x, e (hg6_centreOf ρ x) = hg6_centreOf ρ' (e x) :=
  hg6_saturated_transport_lemma ρ ρ' e he

theorem hg6_isotypic_comparison_aux :
    ∃ Θ : hg_eqH1 hg4_sigmaK b4b_root →ₗ[hp_K] ((ℚ ⊗[ℤ] hg6_cellLattice) →ₗ[ℚ] hp_K),
      Function.Injective Θ ∧
      (∀ φ, φ ∈ LinearMap.range Θ ↔
        ∀ x, φ (hg6_cellJ x) = QuadraticAlgebra.omega * φ x) ∧
      ∀ (c : hg_eqCocycles hg4_sigmaK b4b_root) (z : LinearMap.ker (hg2_bd1 ℤ b4b_root))
        (hz : (Submodule.Quotient.mk z : hg2_H1 ℤ b4b_root) ∈ hg6_cellLattice),
        Θ (Submodule.Quotient.mk c) ((1 : ℚ) ⊗ₜ[ℤ] ⟨Submodule.Quotient.mk z, hz⟩) =
          hg6_pairVec c.1 z.1 0 :=
  hg6_isotypic_comparison_lemma

theorem hg6_coordCup_schur_aux (α β : hg_Edge b4b_Group 13 → Fin 4 → hp_K)
    (hα : α ∈ hg_eqCochain1 hg4_sigmaK) (hβ : β ∈ hg_eqCochain1 hg4_sigmaK) (i j : Fin 4) :
    hg6_coordCup b4b_root i j α β =
      if i = j then (4 : hp_K)⁻¹ * hg4_cupForm b4b_root 1 α β else 0 :=
  hg6_coordCup_schur_lemma α β hα hβ i j

theorem hg6_lattice_not_deck_stable_aux :
    ∃ h : b4b_Group, ∃ x ∈ hg6_cellLattice, hg2_H1act ℤ b4b_root h x ∉ hg6_cellLattice :=
  hg6_lattice_not_deck_stable_lemma

end HodgeLean.Foundations.Program
