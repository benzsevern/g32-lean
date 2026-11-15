import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveChartAlgebra

/-! # Coordinates of the actual normalized projective polynomial line -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- The actual homogeneous coordinate vector of the normalized chart line is
its residue vector plus the parameter times its variation vector.
Source: Hartshorne, Algebraic Geometry, II.7 and II.8, normalized coordinates. -/
theorem s2e_u1_projectiveChartLine_coordinates {n : ℕ} (i : Fin (n + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading n)
      (MvPolynomial.X i : UniversalRing n) →+* DualNumber ℂ) (t : ℂ) :
    vectorOfAwayRingHom i
      ((Polynomial.aeval t).toRingHom.comp (s2e_u1_projectiveChartLine i φ)) =
        (fun j => (φ (chartCoordinate i j)).fst) +
          t • (fun j => (φ (chartCoordinate i j)).snd) := by
  funext j
  simp only [vectorOfAwayRingHom_apply, RingHom.comp_apply,
    s2e_u1_projectiveChartLine, chartAwayPolynomialHom_chartCoordinate]
  by_cases hji : j = i
  · subst j
    simp [chartCoordinate_self]
  · simp [hji, MvPolynomial.eval₂Hom_X', Polynomial.coe_aeval_eq_eval,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_comm (φ (chartCoordinate i j)).snd t

/-- At the actual zero parameter, normalized polynomial chart evaluation is
the residue of the original dual-number chart evaluation.
Source: Hartshorne, Algebraic Geometry, II.8, reduction of a tangent vector. -/
theorem s2e_u1_projectiveChartLine_zero {n : ℕ} (i : Fin (n + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading.{0} n)
      (MvPolynomial.X i : UniversalRing.{0} n) →+* DualNumber ℂ) :
    (Polynomial.aeval (0 : ℂ)).toRingHom.comp (s2e_u1_projectiveChartLine.{0, 0} i φ) =
      (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp φ := by
  apply s2e_u1_projective_chart_ringHom_ext i
  intro j
  have h := congrFun (s2e_u1_projectiveChartLine_coordinates.{0, 0} i φ 0) j
  change ((Polynomial.aeval (0 : ℂ)).toRingHom.comp
    (s2e_u1_projectiveChartLine.{0, 0} i φ)) (chartCoordinate i j) =
      (φ (chartCoordinate i j)).fst
  simpa only [zero_smul, add_zero, vectorOfAwayRingHom_apply] using h

end HodgeLean.Foundations.Program
