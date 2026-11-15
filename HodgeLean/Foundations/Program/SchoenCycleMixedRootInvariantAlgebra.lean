import HodgeLean.Foundations.Program.SchoenCycleMixedRootFormalCoordinates
import HodgeLean.Foundations.Program.SchoenCycleInvariantScalarRestriction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Mixed elementary formal coordinates identify with the actual complex invariant subalgebra of independent root-block permutations.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_mixed_root_complex_invariant_coordinates (b : ℕ) (m : Fin b → ℕ) :
    let P := MvPolynomial (Σ a, Fin (m a)) ℂ
    let O := idealOfVars (Σ a, Fin (m a)) ℂ
    let β (ρ : (a : Fin b) → Equiv.Perm (Fin (m a))) := s2e_adic_algebra_map O O
      (rename (Equiv.Perm.sigmaCongrRight ρ))
      (s2e_rename_preserves_origin_powers (Equiv.Perm.sigmaCongrRight ρ))
    AdicCompletion O P ≃ₐ[ℂ]
      (⨅ ρ, AlgHom.equalizer (β ρ) (AlgHom.id ℂ (AdicCompletion O P)) :
        Subalgebra ℂ (AdicCompletion O P)) := by
  classical
  dsimp only
  let P := MvPolynomial (Σ a, Fin (m a)) ℂ
  let O := idealOfVars (Σ a, Fin (m a)) ℂ
  let α := s2e_mixed_polynomial_action ℂ b m
  let F : Subalgebra ℂ P := ⨅ g, AlgHom.equalizer (α g).toAlgHom (AlgHom.id ℂ P)
  let γ := s2e_invariant_coefficient_base_action α
  let a ρ := s2e_adic_algebra_map O O (γ ρ).toAlgHom
    (s2e_rename_preserves_origin_powers (Equiv.Perm.sigmaCongrRight ρ))
  exact (s2e_mixed_root_formal_coordinates b m).trans
    (s2e_invariant_restrict_scalars_equiv (k := ℂ) a)

end HodgeLean.Foundations.Program
