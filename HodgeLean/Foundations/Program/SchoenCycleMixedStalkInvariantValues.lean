import HodgeLean.Foundations.Program.SchoenCycleMixedStalkInvariantCoordinates
import HodgeLean.Foundations.Program.SchoenCycleMixedFormalStabilizerValues
import HodgeLean.Foundations.Program.SchoenCycleInvariantCoordinateValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The mixed formal geometric invariant comparison evaluates every coefficient polynomial in the actual curve-power stalk parameters.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_mixed_formal_stalk_invariant_values
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n b : ℕ) (x : ComplexPoint (g3_power Z n))
    (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a)
    (q : MvPolynomial (Σ a, Fin (m a)) ℂ) :
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    (s2e_mixed_formal_stalk_invariant_coordinates Z n b x m ι p hp hx
      (AdicCompletion.of (idealOfVars (Σ a, Fin (m a)) ℂ)
        (MvPolynomial (Σ a, Fin (m a)) ℂ) q)).val =
      AdicCompletion.of (IsLocalRing.maximalIdeal R) R
        (aeval (s2e_curvePowerParameter Z n x)
          (rename ι (s2e_mixed_polynomial_invariant_coordinates ℂ b m q).val)) := by
  dsimp only
  letI : Algebra ℂ ((g3_power Z n).left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  unfold s2e_mixed_formal_stalk_invariant_coordinates s2e_curve_power_formal_stabilizer_invariants_equiv
  simp only [id_eq, AlgEquiv.trans_apply]
  erw [s2e_intertwining_invariant_coordinates_val, s2e_mixed_formal_stabilizer_values]
  apply AdicCompletion.ext
  intro N
  rfl

#print axioms s2e_mixed_formal_stalk_invariant_values
end HodgeLean.Foundations.Program
