import HodgeLean.Foundations.Program.SchoenCycleMixedPolynomialGenerators
import Mathlib.RingTheory.MvPolynomial.Ideal

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The extended mixed coefficient-origin ideal has exactly the actual block elementary generators.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_mixed_extended_coefficient_ideal
    (R : Type*) [CommRing R] (b : ℕ) (m : Fin b → ℕ) :
    let P := MvPolynomial (Σ a, Fin (m a)) R
    let F := (⨅ ρ : (a : Fin b) → Equiv.Perm (Fin (m a)),
      AlgHom.equalizer (rename (Equiv.Perm.sigmaCongrRight ρ)) (AlgHom.id R P) : Subalgebra R P)
    let e := s2e_mixed_polynomial_invariant_coordinates R b m
    ((idealOfVars (Σ a, Fin (m a)) R).map e.toRingHom).map (algebraMap F P) =
      Ideal.span (Set.range (fun v : Σ a, Fin (m a) =>
        rename (Sigma.mk v.1) (esymm (Fin (m v.1)) R (v.2.val + 1)))) := by
  dsimp only
  rw [Ideal.map_map, idealOfVars, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext v
  exact s2e_mixed_polynomial_invariant_X R b m v.1 v.2

end HodgeLean.Foundations.Program
