import HodgeLean.Foundations.Program.SchoenCycleSmoothPowerJets

/-! # Polynomial power tests in actual smooth curve-power stalks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual power's regular parameters detect polynomial membership in
every positive total-order coordinate power ideal.
Source: Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald,
Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_curve_power_parameter_polynomial_mem_power_iff
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (x : ComplexPoint (g3_power Z n)) (N : ℕ) (hN : 0 < N)
    (p : MvPolynomial (Fin n) ℂ) :
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    aeval (s2e_curvePowerParameter Z n x) p ∈ IsLocalRing.maximalIdeal R ^ N ↔
      p ∈ idealOfVars (Fin n) ℂ ^ N := by
  let R := (g3_power Z n).left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  obtain ⟨e, he⟩ := s2e_smooth_curve_power_stalk_finite_coordinates Z n x N hN
  constructor
  · intro hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.injective
    rw [he, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
  · intro hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← he, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

/-- Every actual stalk element on a curve power has a parameter polynomial
representative at each positive total jet order.
Source: Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald,
Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_curve_power_parameter_polynomial_representative
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (x : ComplexPoint (g3_power Z n)) (N : ℕ) (hN : 0 < N)
    (r : (g3_power Z n).left.presheaf.stalk x.underlying) :
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ p : MvPolynomial (Fin n) ℂ,
      r - aeval (s2e_curvePowerParameter Z n x) p ∈ IsLocalRing.maximalIdeal R ^ N := by
  let R := (g3_power Z n).left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  obtain ⟨e, he⟩ := s2e_smooth_curve_power_stalk_finite_coordinates Z n x N hN
  obtain ⟨v, hv⟩ := e.surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) r)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hp : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N)
      (aeval (s2e_curvePowerParameter Z n x) p) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ N) r := (he p).symm.trans hv
  refine ⟨p, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  rw [map_sub, hp, sub_self]

end HodgeLean.Foundations.Program
