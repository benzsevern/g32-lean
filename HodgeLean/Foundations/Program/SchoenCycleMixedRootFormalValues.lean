import HodgeLean.Foundations.Program.SchoenCycleInvariantScalarValues
import HodgeLean.Foundations.Program.SchoenCycleMixedRootInvariantAlgebra
import HodgeLean.Foundations.Program.SchoenCycleMixedRootFormalCoordinates
import HodgeLean.Foundations.Program.SchoenCycleMixedFormalCoefficientValues
import HodgeLean.Foundations.Program.SchoenCycleInvariantCoordinateValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The mixed origin-adic coefficient comparison retains exact elementary root substitution on every coefficient polynomial.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_mixed_root_formal_values (b : ℕ) (m : Fin b → ℕ)
    (p : MvPolynomial (Σ a, Fin (m a)) ℂ) :
    let P := MvPolynomial (Σ a, Fin (m a)) ℂ
    let O := idealOfVars (Σ a, Fin (m a)) ℂ
    (s2e_mixed_root_formal_coordinates b m (AdicCompletion.of O P p)).val =
      AdicCompletion.of O P (s2e_mixed_polynomial_invariant_coordinates ℂ b m p).val := by
  dsimp only
  unfold s2e_mixed_root_formal_coordinates
  simp only [id_eq, AlgEquiv.trans_apply, AlgEquiv.symm_restrictScalars, AlgEquiv.restrictScalars_apply]
  rw [s2e_intertwining_invariant_coordinates_symm_val, s2e_mixed_formal_coefficient_values]
  apply AdicCompletion.ext
  intro n
  rfl

#print axioms s2e_mixed_root_formal_values

/-- Restricting to the actual complex invariant subalgebra preserves exact elementary root values.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_mixed_root_complex_values (b : ℕ) (m : Fin b → ℕ)
    (p : MvPolynomial (Σ a, Fin (m a)) ℂ) :
    let P := MvPolynomial (Σ a, Fin (m a)) ℂ
    let O := idealOfVars (Σ a, Fin (m a)) ℂ
    (s2e_mixed_root_complex_invariant_coordinates b m (AdicCompletion.of O P p)).val =
      AdicCompletion.of O P (s2e_mixed_polynomial_invariant_coordinates ℂ b m p).val := by
  dsimp only
  unfold s2e_mixed_root_complex_invariant_coordinates
  simp only [id_eq, AlgEquiv.trans_apply]
  erw [s2e_invariant_restrict_scalars_val]
  exact s2e_mixed_root_formal_values b m p

#print axioms s2e_mixed_root_complex_values
end HodgeLean.Foundations.Program
