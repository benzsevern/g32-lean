import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartRings

/-! # Polynomial coordinates in the actual projective chart -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- Integral polynomials evaluate at the actual regular coordinate ratios of the projective chart.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
def s2e_integralPolynomialToChart {n : ℕ} (i : Fin (n + 1)) :
    UniversalRing n →+*
      HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom
    ((algebraMap ℤ (HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i))).comp
      ULift.ringEquiv.toRingHom) (chartCoordinate i)

example {n : ℕ} (i j : Fin (n + 1)) :
    s2e_integralPolynomialToChart i (MvPolynomial.X j) = chartCoordinate i j := by
  simp only [s2e_integralPolynomialToChart, MvPolynomial.eval₂Hom_X']

/-- The normalized integral polynomial quotient maps to the actual chart because the selected ratio equals one.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
def s2e_normalizedPolynomialToChart {n : ℕ} (i : Fin (n + 1)) :
    UniversalRing n ⧸ Ideal.span ({MvPolynomial.X i - 1} : Set (UniversalRing n)) →+*
      HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) :=
  Ideal.Quotient.lift _ (s2e_integralPolynomialToChart i) (by
    change Ideal.span ({MvPolynomial.X i - 1} : Set (UniversalRing n)) ≤
      RingHom.ker (s2e_integralPolynomialToChart i)
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    change s2e_integralPolynomialToChart i (MvPolynomial.X i - 1) = 0
    simp only [map_sub, map_one, s2e_integralPolynomialToChart,
      MvPolynomial.eval₂Hom_X', chartCoordinate_self, sub_self])

example {n : ℕ} (i j : Fin (n + 1)) :
    s2e_normalizedPolynomialToChart i
      (Ideal.Quotient.mk (Ideal.span ({MvPolynomial.X i - 1} : Set (UniversalRing n)))
        (MvPolynomial.X j)) = chartCoordinate i j := by
  simp only [s2e_normalizedPolynomialToChart, Ideal.Quotient.lift_mk,
    s2e_integralPolynomialToChart, MvPolynomial.eval₂Hom_X']

/-- Passing through normalized polynomial coordinates preserves every element of the actual integral chart ring.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
theorem s2e_integral_chart_polynomial_retraction {n : ℕ} (i : Fin (n + 1)) :
    (s2e_integralPolynomialToChart i).comp (s2e_integralChartAwayHom i) =
      RingHom.id (HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i)) := by
  refine s2e_projective_chart_ringHom_ext
    (T := HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i)) i
    ((s2e_integralPolynomialToChart i).comp (s2e_integralChartAwayHom i)) (RingHom.id _) ?_ ?_
  · intro a
    let η := HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
      (Submonoid.powers (MvPolynomial.X i : UniversalRing n))
    exact DFunLike.congr_fun (s2e_projective_degreeZero_ringHom_unique
      (((s2e_integralPolynomialToChart i).comp (s2e_integralChartAwayHom i)).comp η)
      ((RingHom.id _).comp η)) a
  · intro j
    simp only [RingHom.comp_apply, RingHom.id_apply, s2e_integralChartAwayHom_coordinate]
    by_cases h : j = i
    · subst j
      simp only [ite_eq_left, map_one, chartCoordinate_self]
    · rw [if_neg h]
      simp only [s2e_integralPolynomialToChart, MvPolynomial.eval₂Hom_X']

end HodgeLean.Foundations.Program
