import HodgeLean.Foundations.Program.SchoenCycleMixedPolynomialAction
import HodgeLean.Foundations.Program.SchoenCycleInvariantCoefficientAction
import HodgeLean.Foundations.Program.SchoenCycleAdicEquivMap
import Mathlib.RingTheory.MvPolynomial.Ideal

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The actual mixed coefficient adic algebra identifies with the block invariants in its extended-ideal root algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_mixed_formal_coefficient_invariants (b : ℕ) (m : Fin b → ℕ) :
    let P := MvPolynomial (Σ a, Fin (m a)) ℂ
    let α := s2e_mixed_polynomial_action ℂ b m
    let F : Subalgebra ℂ P := ⨅ g, AlgHom.equalizer (α g).toAlgHom (AlgHom.id ℂ P)
    let e := s2e_mixed_polynomial_invariant_coordinates ℂ b m
    let I := (idealOfVars (Σ a, Fin (m a)) ℂ).map e.toRingHom
    let J := I.map (algebraMap F P)
    let γ := s2e_invariant_coefficient_base_action α
    let β g := s2e_adic_algebra_map J J (γ g).toAlgHom
      (s2e_linear_preserves_extended_ideal_powers I (γ g).toLinearMap)
    AdicCompletion (idealOfVars (Σ a, Fin (m a)) ℂ) P ≃ₐ[ℂ]
      (⨅ g, AlgHom.equalizer (β g) (AlgHom.id F (AdicCompletion J P)) :
        Subalgebra F (AdicCompletion J P)) := by
  classical
  dsimp only
  let e := s2e_mixed_polynomial_invariant_coordinates ℂ b m
  let I := (idealOfVars (Σ a, Fin (m a)) ℂ).map e.toRingHom
  exact (s2e_adic_equiv_map (idealOfVars (Σ a, Fin (m a)) ℂ) e).trans
    ((s2e_invariant_coefficient_adic_equiv (s2e_mixed_polynomial_action ℂ b m) I).restrictScalars ℂ)

end HodgeLean.Foundations.Program
