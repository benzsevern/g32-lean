import HodgeLean.Foundations.Program.SchoenCycleMixedFormalStabilizer
import HodgeLean.Foundations.Program.SchoenCycleMixedRootFormalValues
import HodgeLean.Foundations.Program.SchoenCycleAdicReindexedInvariantValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual mixed tuple-stabilizer formal comparison retains the indexed elementary root values of every coefficient polynomial.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_mixed_formal_stabilizer_values
    (Z : Over (Spec ↧ℂ)) (n b : ℕ) (x : ComplexPoint (g3_power Z n))
    (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a)
    (q : MvPolynomial (Σ a, Fin (m a)) ℂ) :
    (s2e_mixed_formal_stabilizer_coordinates Z n b x m ι p hp hx
      (AdicCompletion.of (idealOfVars (Σ a, Fin (m a)) ℂ)
        (MvPolynomial (Σ a, Fin (m a)) ℂ) q)).val =
      AdicCompletion.of (idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ)
        (rename ι (s2e_mixed_polynomial_invariant_coordinates ℂ b m q).val) := by
  unfold s2e_mixed_formal_stabilizer_coordinates
  simp only [id_eq, AlgEquiv.trans_apply]
  rw [s2e_adic_reindexed_invariants_val, s2e_mixed_root_complex_values]
  apply AdicCompletion.ext
  intro N
  rfl

#print axioms s2e_mixed_formal_stabilizer_values
end HodgeLean.Foundations.Program
