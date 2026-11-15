import HodgeLean.Foundations.Program.SchoenCycleMixedFormalCoefficientAlgebra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The formal mixed coefficient comparison evaluates every coefficient polynomial at its actual elementary root coefficients.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_mixed_formal_coefficient_values (b : ℕ) (m : Fin b → ℕ)
    (p : MvPolynomial (Σ a, Fin (m a)) ℂ) :
    let P := MvPolynomial (Σ a, Fin (m a)) ℂ
    let α := s2e_mixed_polynomial_action ℂ b m
    let F : Subalgebra ℂ P := ⨅ g, AlgHom.equalizer (α g).toAlgHom (AlgHom.id ℂ P)
    let e := s2e_mixed_polynomial_invariant_coordinates ℂ b m
    let O := idealOfVars (Σ a, Fin (m a)) ℂ
    let I := O.map e.toRingHom
    let J := I.map (algebraMap F P)
    (s2e_mixed_formal_coefficient_invariants b m (AdicCompletion.of O P p)).val =
      AdicCompletion.of J P (e p).val := by
  dsimp only
  apply AdicCompletion.ext
  intro n
  rfl

#print axioms s2e_mixed_formal_coefficient_values
end HodgeLean.Foundations.Program
