import HodgeLean.Foundations.Program.SchoenCycleMixedFormalCoefficientAlgebra
import HodgeLean.Foundations.Program.SchoenCycleMixedExtendedIdeal
import HodgeLean.Foundations.Program.SchoenCycleSigmaCoefficientCofinality
import HodgeLean.Foundations.Program.SchoenCycleElementaryIdealInclusion
import HodgeLean.Foundations.Program.SchoenCycleAdicCofinalAction
import HodgeLean.Foundations.Program.SchoenCycleIntertwiningInvariantAlgebras
import HodgeLean.Foundations.Program.SchoenCycleRenamedAdicPowers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Formal elementary coordinates in every indexed block are the independent block invariants of the actual root-origin adic algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
def s2e_mixed_root_formal_coordinates (b : ℕ) (m : Fin b → ℕ) :
    let P := MvPolynomial (Σ a, Fin (m a)) ℂ
    let O := idealOfVars (Σ a, Fin (m a)) ℂ
    let α := s2e_mixed_polynomial_action ℂ b m
    let F : Subalgebra ℂ P := ⨅ g, AlgHom.equalizer (α g).toAlgHom (AlgHom.id ℂ P)
    let γ := s2e_invariant_coefficient_base_action α
    let β g := s2e_adic_algebra_map O O (γ g).toAlgHom
      (s2e_rename_preserves_origin_powers (Equiv.Perm.sigmaCongrRight g))
    AdicCompletion O P ≃ₐ[ℂ]
      (⨅ g, AlgHom.equalizer (β g) (AlgHom.id F (AdicCompletion O P)) :
        Subalgebra F (AdicCompletion O P)) := by
  classical
  dsimp only
  let P := MvPolynomial (Σ a, Fin (m a)) ℂ
  let O := idealOfVars (Σ a, Fin (m a)) ℂ
  let α := s2e_mixed_polynomial_action ℂ b m
  let F : Subalgebra ℂ P := ⨅ g, AlgHom.equalizer (α g).toAlgHom (AlgHom.id ℂ P)
  let γ := s2e_invariant_coefficient_base_action α
  let e := s2e_mixed_polynomial_invariant_coordinates ℂ b m
  let I := O.map e.toRingHom
  let J := I.map (algebraMap F P)
  have hJ : J = Ideal.span (Set.range (fun v : Σ a, Fin (m a) =>
      rename (Sigma.mk v.1) (esymm (Fin (m v.1)) ℂ (v.2.val + 1)))) :=
    s2e_mixed_extended_coefficient_ideal ℂ b m
  have hJO : J ≤ O := by
    rw [hJ]
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨a, j⟩, rfl⟩
    have hp := s2e_positive_elementary_mem_origin (σ := Fin (m a)) (j.val + 1) (by omega)
    have hh := s2e_rename_preserves_origin_powers (fun i : Fin (m a) => (⟨a, i⟩ : Σ a, Fin (m a))) 1 _ (by simpa using hp)
    change rename (fun i : Fin (m a) => (⟨a, i⟩ : Σ a, Fin (m a)))
      (esymm (Fin (m a)) ℂ (j.val + 1)) ∈ idealOfVars (Σ a, Fin (m a)) ℂ
    simpa only [pow_one] using hh
  let c := Classical.choose (s2e_sigma_origin_power_le_coefficient_ideal b m)
  have hc := Classical.choose_spec (s2e_sigma_origin_power_le_coefficient_ideal b m)
  have hc' : O ^ (c + 1) ≤ J := by
    rw [hJ]
    exact (Ideal.pow_le_pow_right (Nat.le_succ c)).trans hc
  let E := s2e_adic_cofinal_equiv (k := F) O J hJO (c + 1) (by omega) hc'
  let a g := s2e_adic_algebra_map O O (γ g).toAlgHom
    (s2e_rename_preserves_origin_powers (Equiv.Perm.sigmaCongrRight g))
  let d g := s2e_adic_algebra_map J J (γ g).toAlgHom
    (s2e_linear_preserves_extended_ideal_powers I (γ g).toLinearMap)
  let D := s2e_intertwining_invariant_algebras_equiv E a d (by
    intro g
    apply AlgHom.ext
    intro x
    exact s2e_adic_cofinal_equiv_intertwines O J hJO (c + 1) (by omega) hc'
      (γ g).toAlgHom (s2e_rename_preserves_origin_powers (Equiv.Perm.sigmaCongrRight g))
      (s2e_linear_preserves_extended_ideal_powers I (γ g).toLinearMap) x)
  exact (s2e_mixed_formal_coefficient_invariants b m).trans (D.restrictScalars ℂ).symm

end HodgeLean.Foundations.Program
