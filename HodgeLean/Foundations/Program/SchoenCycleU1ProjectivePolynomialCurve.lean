import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveDualLines
import HodgeLean.Foundations.Program.SchoenCycleU1PolynomialParameterPoint

/-! # Normalized actual polynomial projective curves -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- The actual projective curve obtained from the normalized polynomial chart line.
Source: Hartshorne, Algebraic Geometry, II.7 and II.8, standard projective charts. -/
def s2e_u1_projectiveChartCurve {n : ℕ} (i : Fin (n + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading.{0} n)
      (MvPolynomial.X i : UniversalRing.{0} n) →+* DualNumber ℂ) :
    s2e_u1_specOver (Polynomial ℂ) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)) :=
  Over.homMk
    (Limits.pullback.lift
      (Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)))
      (Spec.map (CommRingCat.ofHom (s2e_u1_projectiveChartLine i φ)) ≫
        Proj.awayι (UniversalGrading.{0} n) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X _ _) zero_lt_one)
      (Subsingleton.elim _ _)) (by exact Limits.pullback.lift_fst _ _ _)

/-- Every actual parameter point on the normalized projective curve has the
homogeneous coordinates recovered from its specified chart evaluation.
Source: Hartshorne, Algebraic Geometry, II.7, standard projective charts. -/
theorem s2e_u1_projectiveChartCurve_point {n : ℕ} (i : Fin (n + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading.{0} n)
      (MvPolynomial.X i : UniversalRing.{0} n) →+* DualNumber ℂ) (t : ℂ) :
    let ψ : HomogeneousLocalization.Away (UniversalGrading.{0} n)
      (MvPolynomial.X i : UniversalRing.{0} n) →+* ℂ :=
    (Polynomial.aeval t).toRingHom.comp (s2e_u1_projectiveChartLine i φ)
    Point.map (s2e_u1_projectiveChartCurve i φ) (s2e_u1_polynomialParameterPoint t) =
      vectorToComplexPoint (vectorOfAwayRingHom i ψ) (vectorOfAwayRingHom_ne_zero i ψ) := by
  let ψ : HomogeneousLocalization.Away (UniversalGrading.{0} n)
      (MvPolynomial.X i : UniversalRing.{0} n) →+* ℂ :=
    (Polynomial.aeval t).toRingHom.comp (s2e_u1_projectiveChartLine i φ)
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · exact (Over.w (Point.map (s2e_u1_projectiveChartCurve i φ)
      (s2e_u1_polynomialParameterPoint t))).trans
        (Over.w (vectorToComplexPoint (vectorOfAwayRingHom i ψ)
          (vectorOfAwayRingHom_ne_zero i ψ))).symm
  · change Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom) ≫
      ((s2e_u1_projectiveChartCurve i φ).left ≫ Limits.pullback.snd _ _) =
        vectorToProjectiveSpace (vectorOfAwayRingHom i ψ)
          (vectorOfAwayRingHom_ne_zero i ψ) ≫ Limits.pullback.snd _ _
    rw [vectorToProjectiveSpace_toProj,
      chartIntegralProj_eq_chartIntegralProjAt _ _ i (by simp)]
    let g0 : Spec (CommRingCat.of (Polynomial ℂ)) ⟶
        ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ) :=
      Limits.pullback.lift
        (Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)))
        (Spec.map (CommRingCat.ofHom (s2e_u1_projectiveChartLine i φ)) ≫
          Proj.awayι (UniversalGrading.{0} n) (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X _ _) zero_lt_one) (Subsingleton.elim _ _)
    change Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom) ≫
      (g0 ≫ Limits.pullback.snd _ _) = chartIntegralProjAt (vectorOfAwayRingHom i ψ) i _
    dsimp only [g0, chartIntegralProjAt]
    rw [Limits.pullback.lift_snd, ← Category.assoc, ← Spec.map_comp]
    have he : CommRingCat.ofHom (s2e_u1_projectiveChartLine i φ) ≫
        CommRingCat.ofHom (Polynomial.aeval t).toRingHom =
      CommRingCat.ofHom (awayCoordinateEvaluation (vectorOfAwayRingHom i ψ) i
        (by simp)) := by
      apply CommRingCat.hom_ext
      change ψ = awayCoordinateEvaluation (vectorOfAwayRingHom i ψ) i (by simp)
      exact (awayCoordinateEvaluation_vectorOfAwayRingHom i ψ).symm
    exact congrArg (fun u => Spec.map u ≫ Proj.awayι (UniversalGrading.{0} n)
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ _) zero_lt_one) he

end HodgeLean.Foundations.Program
