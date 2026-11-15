import HodgeLean.Foundations.Program.SchoenCycleSmoothPowerJets

/-! # Nonvanishing of actual regular coordinate parameters -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every actual curve-power coordinate parameter has a nonzero first-order class and hence is nonzero.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_curvePowerParameter_ne_zero
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (x : ComplexPoint (g3_power Z n)) (i : Fin n) :
    s2e_curvePowerParameter Z n x i ≠ 0 := by
  let R := (g3_power Z n).left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  intro hi
  obtain ⟨e, he⟩ := s2e_smooth_curve_power_stalk_finite_coordinates Z n x 2 (by omega)
  have h := he (X i)
  rw [aeval_X, hi, map_zero] at h
  have hz : Ideal.Quotient.mk (idealOfVars (Fin n) ℂ ^ 2) (X i) = 0 :=
    e.injective (h.trans (map_zero e).symm)
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
  change monomial (Finsupp.single i 1) (1 : ℂ) ∈ idealOfVars (Fin n) ℂ ^ 2 at hm
  have hn := (monomial_mem_pow_idealOfVars_iff 2 (Finsupp.single i 1) (one_ne_zero : (1 : ℂ) ≠ 0)).mp hm
  norm_num only [Finsupp.degree_single] at hn

end HodgeLean.Foundations.Program
