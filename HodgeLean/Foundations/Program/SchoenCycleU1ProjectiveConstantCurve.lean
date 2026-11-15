import HodgeLean.Foundations.Program.SchoenCycleU1ProjectivePolynomialCurve
import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveLineCoordinates
import HodgeLean.Foundations.Program.SchoenCycleU1PolynomialDualParameter
import HodgeLean.Foundations.Program.SchoenCycleU1ConstantDualPoint

/-! # Constant actual projective dual restrictions -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- A constant normalized dual chart evaluation gives the actual constant
projective dual point at the actual zero-parameter point of its chart curve.
Source: Hartshorne, Algebraic Geometry, II.7 and II.8. -/
theorem s2e_u1_projectiveChartCurve_dual_constant {n : ℕ} (i : Fin (n + 1))
    (φ : HomogeneousLocalization.Away (UniversalGrading.{0} n)
      (MvPolynomial.X i : UniversalRing.{0} n) →+* DualNumber ℂ)
    (hφ : φ = (TrivSqZeroExt.inlHom ℂ ℂ).comp
      ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp φ)) :
    s2e_u1_polynomialDualParameter ≫ s2e_u1_projectiveChartCurve i φ =
      s2e_u1_constantDualPoint _
        (Point.map (s2e_u1_projectiveChartCurve i φ) (s2e_u1_polynomialParameterPoint 0)) := by
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))
  let line := s2e_u1_projectiveChartLine.{0, 0} i φ
  let g0 : Spec (CommRingCat.of (Polynomial ℂ)) ⟶
      ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ) :=
    Limits.pullback.lift
      (Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)))
      (Spec.map (CommRingCat.ofHom line) ≫
        Proj.awayι (UniversalGrading.{0} n) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X _ _) zero_lt_one) (Subsingleton.elim _ _)
  have he : CommRingCat.ofHom line ≫ CommRingCat.ofHom
      (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ)).toRingHom =
      CommRingCat.ofHom line ≫ CommRingCat.ofHom (Polynomial.aeval (0 : ℂ)).toRingHom ≫
        CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) := by
    apply CommRingCat.hom_ext
    change (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ)).toRingHom.comp line =
      (TrivSqZeroExt.inlHom ℂ ℂ).comp
        ((Polynomial.aeval (0 : ℂ)).toRingHom.comp line)
    rw [show (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ)).toRingHom.comp line = φ
      from s2e_u1_projectiveChartLine_dual i φ,
      s2e_u1_projectiveChartLine_zero]
    exact hφ
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · exact (Over.w (s2e_u1_polynomialDualParameter ≫ s2e_u1_projectiveChartCurve i φ)).trans
      (Over.w (s2e_u1_constantDualPoint PP
        (Point.map (s2e_u1_projectiveChartCurve i φ) (s2e_u1_polynomialParameterPoint 0)))).symm
  · change Spec.map (CommRingCat.ofHom
        (Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ)).toRingHom) ≫
        (g0 ≫ Limits.pullback.snd _ _) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫
        ((Spec.map (CommRingCat.ofHom (Polynomial.aeval (0 : ℂ)).toRingHom) ≫ g0) ≫
          Limits.pullback.snd _ _)
    dsimp only [g0]
    simp only [Category.assoc, Limits.pullback.lift_snd, ← Spec.map_comp_assoc]
    exact congrArg (fun u => Spec.map u ≫ Proj.awayι (UniversalGrading.{0} n)
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ _) zero_lt_one) he

end HodgeLean.Foundations.Program
