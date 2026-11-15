import HodgeLean.Foundations.Program.SchoenCycleSmoothPowerJets

/-! # Exact finite order of actual coordinate parameter products -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- A product of selected actual coordinate parameters does not vanish in the next total-order neighbourhood.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_curvePowerParameter_product_not_mem_next_power
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (x : ComplexPoint (g3_power Z n)) (S : Finset (Fin n)) :
    (∏ i ∈ S, s2e_curvePowerParameter Z n x i) ∉
      IsLocalRing.maximalIdeal ((g3_power Z n).left.presheaf.stalk x.underlying) ^ (S.card + 1) := by
  let R := (g3_power Z n).left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  intro hm
  obtain ⟨e, he⟩ := s2e_smooth_curve_power_stalk_finite_coordinates Z n x (S.card + 1) (by omega)
  let P : MvPolynomial (Fin n) ℂ := ∏ i ∈ S, X i
  have hv : aeval (s2e_curvePowerParameter Z n x) P =
      ∏ i ∈ S, s2e_curvePowerParameter Z n x i := by
    dsimp only [P]
    rw [map_prod]
    simp only [aeval_X]
  have hz : e (Ideal.Quotient.mk (idealOfVars (Fin n) ℂ ^ (S.card + 1)) P) = 0 := by
    rw [he P, hv, Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  have hz' := e.injective (hz.trans (map_zero e).symm)
  have hP : P = monomial (∑ i ∈ S, Finsupp.single i 1) 1 :=
    (monomial_sum_one S (fun i => Finsupp.single i 1)).symm
  have hp := Ideal.Quotient.eq_zero_iff_mem.mp hz'
  rw [hP, monomial_mem_pow_idealOfVars_iff _ _ (one_ne_zero : (1 : ℂ) ≠ 0)] at hp
  have hd : Finsupp.degree (∑ i ∈ S, Finsupp.single i 1) = S.card := by
    simp only [map_sum, Finsupp.degree_single, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]
  rw [hd] at hp
  exact Nat.not_succ_le_self S.card hp

end HodgeLean.Foundations.Program
