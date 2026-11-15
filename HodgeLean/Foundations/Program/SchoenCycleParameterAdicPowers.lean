import HodgeLean.Foundations.Program.SchoenCycleSmoothPowerJets

/-! # Adic filtration of actual curve-power parameters -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Evaluation in the actual point-indexed parameters preserves every power of the origin ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_curve_power_aeval_preserves_powers
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (x : ComplexPoint (g3_power X n)) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∀ N : ℕ, ∀ p ∈ idealOfVars (Fin n) ℂ ^ N,
      aeval (s2e_curvePowerParameter X n x) p ∈ IsLocalRing.maximalIdeal R ^ N := by
  dsimp only
  letI : Algebra ℂ ((g3_power X n).left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  intro N p hp
  by_cases hN : N = 0
  · subst N
    simpa only [pow_zero, Ideal.one_eq_top] using
      (show aeval (s2e_curvePowerParameter X n x) p ∈
        (⊤ : Ideal ((g3_power X n).left.presheaf.stalk x.underlying)) from trivial)
  obtain ⟨e, he⟩ := s2e_smooth_curve_power_stalk_finite_coordinates X n x N (Nat.pos_of_ne_zero hN)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [← he p, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

#print axioms s2e_curve_power_aeval_preserves_powers
end HodgeLean.Foundations.Program
