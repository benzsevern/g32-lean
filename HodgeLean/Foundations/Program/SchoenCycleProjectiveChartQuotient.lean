import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartNormalization

/-! # The actual projective chart as a normalized polynomial quotient -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- The actual chart coordinate map recovers every normalized polynomial residue class.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
theorem s2e_integral_chart_quotient_section {n : ℕ} (i : Fin (n + 1)) :
    ((Ideal.Quotient.mk (Ideal.span ({MvPolynomial.X i - 1} : Set (UniversalRing n)))).comp
      (s2e_integralChartAwayHom i)).comp (s2e_normalizedPolynomialToChart i) =
      RingHom.id (UniversalRing n ⧸ Ideal.span ({MvPolynomial.X i - 1} : Set (UniversalRing n))) := by
  let I := Ideal.span ({MvPolynomial.X i - 1} : Set (UniversalRing n))
  let π := Ideal.Quotient.mk I
  let ψ := π.comp (s2e_integralChartAwayHom i)
  have hXi : π (MvPolynomial.X i) = 1 := by
    have hz : π (MvPolynomial.X i - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    simpa only [map_sub, map_one, sub_eq_zero] using hz
  have hcomp : (ψ.comp (s2e_normalizedPolynomialToChart i)).comp π = π := by
    apply MvPolynomial.ringHom_ext'
    · let f := ((ψ.comp (s2e_normalizedPolynomialToChart i)).comp π).comp MvPolynomial.C
      let g := π.comp MvPolynomial.C
      apply RingHom.ext
      intro a
      obtain ⟨z, rfl⟩ := (ULift.ringEquiv (R := ℤ)).symm.surjective a
      exact DFunLike.congr_fun (Subsingleton.elim
        (f.comp (ULift.ringEquiv (R := ℤ)).symm.toRingHom)
        (g.comp (ULift.ringEquiv (R := ℤ)).symm.toRingHom)) z
    · intro j
      change π (s2e_integralChartAwayHom i
        (s2e_integralPolynomialToChart i (MvPolynomial.X j))) = π (MvPolynomial.X j)
      rw [show s2e_integralPolynomialToChart i (MvPolynomial.X j) = chartCoordinate i j by
        simp only [s2e_integralPolynomialToChart, MvPolynomial.eval₂Hom_X']]
      rw [s2e_integralChartAwayHom_coordinate]
      by_cases h : j = i
      · subst j
        simpa only [ite_eq_left, map_one] using hXi.symm
      · rw [if_neg h]
  apply Ideal.Quotient.ringHom_ext
  simpa only [RingHom.id_comp] using hcomp

/-- The actual integral standard projective chart ring is the normalized polynomial quotient.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Hartshorne, Algebraic Geometry, II.2 and II.7. -/
def s2e_integralChartRingEquiv {n : ℕ} (i : Fin (n + 1)) :
    HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) ≃+*
      UniversalRing n ⧸ Ideal.span ({MvPolynomial.X i - 1} : Set (UniversalRing n)) where
  __ := (Ideal.Quotient.mk (Ideal.span ({MvPolynomial.X i - 1} : Set (UniversalRing n)))).comp
    (s2e_integralChartAwayHom i)
  invFun := s2e_normalizedPolynomialToChart i
  left_inv r := DFunLike.congr_fun (s2e_integral_chart_polynomial_retraction i) r
  right_inv q := DFunLike.congr_fun (s2e_integral_chart_quotient_section i) q

example {n : ℕ} (i j : Fin (n + 1)) :
    s2e_integralChartRingEquiv i (chartCoordinate i j) =
      Ideal.Quotient.mk (Ideal.span ({MvPolynomial.X i - 1} : Set (UniversalRing n)))
        (if j = i then 1 else MvPolynomial.X j) := by
  change Ideal.Quotient.mk _ (s2e_integralChartAwayHom i (chartCoordinate i j)) = _
  rw [s2e_integralChartAwayHom_coordinate]

end HodgeLean.Foundations.Program
