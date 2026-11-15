import HodgeLean.Foundations.Program.SchoenCycleAdicMapBijective
import HodgeLean.Foundations.Program.SchoenCycleParameterAdicPowers

/-! # Canonical formal coordinates induced by actual parameter evaluation -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Formal coordinates whose forward map is the actual adic parameter-evaluation map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald, Chapter 10. -/
def s2e_curve_power_adic_equiv
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (x : ComplexPoint (g3_power X n)) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    AdicCompletion (idealOfVars (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) ≃ₐ[ℂ]
      AdicCompletion (IsLocalRing.maximalIdeal R) R := by
  dsimp only
  letI : Algebra ℂ ((g3_power X n).left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  refine AlgEquiv.ofBijective
    (s2e_adic_algebra_map _ _ (aeval (s2e_curvePowerParameter X n x))
      (s2e_curve_power_aeval_preserves_powers X n x)) ?_
  apply s2e_adic_algebra_map_bijective
  intro N
  by_cases hN : N = 0
  · subst N
    letI : Subsingleton (MvPolynomial (Fin n) ℂ ⧸ idealOfVars (Fin n) ℂ ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    letI : Subsingleton (((g3_power X n).left.presheaf.stalk x.underlying) ⧸
        IsLocalRing.maximalIdeal ((g3_power X n).left.presheaf.stalk x.underlying) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact ⟨default, fun _ => Subsingleton.elim _ _⟩
  · exact s2e_smooth_curve_power_stalk_finite_coordinates X n x N (Nat.pos_of_ne_zero hN)

#print axioms s2e_curve_power_adic_equiv
end HodgeLean.Foundations.Program
