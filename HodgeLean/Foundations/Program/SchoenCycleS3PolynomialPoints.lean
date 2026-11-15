import HodgeLean.Foundations.Program.SchoenCycleS3LinearProj
import HodgeLean.Foundations.Program.SchoenPolynomialProjectivePermutations
import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints

/-! # Evaluation points of complex polynomial projective spectra -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- Evaluate the degree-zero localization of a complex polynomial chart. -/
def s2e_complexPolynomialChartEvaluation {k : ℕ} (v : CoordinateSpace k)
    (f : MvPolynomial (Fin (k + 1)) ℂ) (hf : eval v f ≠ 0) :
    Away (homogeneousSubmodule (Fin (k + 1)) ℂ) f →+* ℂ :=
  (Localization.awayLift (eval v) f (isUnit_iff_ne_zero.mpr hf)).comp
    (algebraMap _ (Localization.Away f))

/-- Homogeneous fractions evaluate as the numerator divided by the denominator power. -/
theorem s2e_complexPolynomialChartEvaluation_mk {k m : ℕ} (v : CoordinateSpace k)
    (f : MvPolynomial (Fin (k + 1)) ℂ) (hf : eval v f ≠ 0)
    (hm : f.IsHomogeneous m) (d : ℕ)
    (p : MvPolynomial (Fin (k + 1)) ℂ) (hp : p.IsHomogeneous (d * m)) :
    s2e_complexPolynomialChartEvaluation v f hf
      (Away.mk (homogeneousSubmodule (Fin (k + 1)) ℂ) hm d p (by simpa using hp)) =
      eval v p * (eval v f)⁻¹ ^ d := by
  change (Localization.awayLift (eval v) f (isUnit_iff_ne_zero.mpr hf))
    (Localization.mk p ⟨f ^ d, ⟨d, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (eval v) f p ((eval v f)⁻¹)]
  exact mul_inv_cancel₀ hf

/-- Evaluation on integral coordinate polynomials is compatible with complex scalar extension. -/
theorem s2e_integralCoordinates_eval {k : ℕ} (v : CoordinateSpace k) :
    (eval v).comp (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))).toRingHom =
      coordinateEvaluationHom v := by
  apply MvPolynomial.ringHom_ext
  · intro c
    have h : c = (c.down : ULift ℤ) := by rfl
    rw [h, map_intCast, map_intCast]
    change ((c.down : ℂ)) = coordinateEvaluationHom v (C (c.down : ULift ℤ))
    rw [map_intCast, map_intCast]
  · intro i
    change eval v (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1)) (X i)) = _
    rw [s2_polynomialIntegralCoordinates_X, eval_X, coordinateEvaluationHom_X]

/-- Complex polynomial chart evaluation agrees with the integral chart evaluation. -/
theorem s2e_complexPolynomialChartEvaluation_integral {k : ℕ} (v : CoordinateSpace k)
    (i : Fin (k + 1)) (hi : v i ≠ 0) :
    (s2e_complexPolynomialChartEvaluation v
      (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1)) (X i))
      (by simpa only [s2_polynomialIntegralCoordinates_X, eval_X] using hi)).comp
      (Away.map (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))) (X i)) =
      awayCoordinateEvaluation v i hi := by
  ext z
  obtain ⟨d, p, hp, rfl⟩ := Away.mk_surjective (UniversalGrading k) (isHomogeneous_X _ i) z
  simp only [RingHom.comp_apply, Away.map_mk]
  rw [s2e_complexPolynomialChartEvaluation_mk (hp := by
    simpa using (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))).map_mem hp),
    awayCoordinateEvaluation_mk (hr := by simpa using hp)]
  simp only [s2_polynomialIntegralCoordinates_X, eval_X]
  exact congrArg (fun z : ℂ => z * (v i)⁻¹ ^ d)
    (RingHom.congr_fun (s2e_integralCoordinates_eval v) p)

/-- The polynomial Proj comparison sends an evaluation point to its actual homogeneous point. -/
theorem s2e_complexPolynomialChartEvaluation_point {k : ℕ} (v : CoordinateSpace k)
    (i : Fin (k + 1)) (hi : v i ≠ 0) :
    Spec.map (CommRingCat.ofHom (s2e_complexPolynomialChartEvaluation v
      (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1)) (X i))
      (by simpa only [s2_polynomialIntegralCoordinates_X, eval_X] using hi))) ≫
      Proj.awayι (homogeneousSubmodule (Fin (k + 1)) ℂ)
        (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1)) (X i))
        ((s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))).map_mem (isHomogeneous_X _ i)) zero_lt_one ≫
      (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom =
      vectorToProjectiveSpace v (vector_ne_zero_of_coordinate v i hi) := by
  apply pullback.hom_ext
  · change (_ ≫ _ ≫ _) ≫ ProjectiveSpace.toBase _ _ = _ ≫ ProjectiveSpace.toBase _ _
    simp only [Category.assoc]
    rw [s2_polynomialProjectiveSpaceIso_toBase,
      Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp,
      vectorToProjectiveSpace_toBase]
    change Spec.map _ = 𝟙 _
    rw [← Spec.map_id]
    congr 1
    ext c
    simp only [RingEquiv.toCommRingCatIso_hom]
    change s2e_complexPolynomialChartEvaluation v
      (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1)) (X i))
      (by simpa only [s2_polynomialIntegralCoordinates_X, eval_X] using hi)
      (fromZeroRingHom (homogeneousSubmodule (Fin (k + 1)) ℂ) (.powers (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1)) (X i)))
        ((ProjectiveSpace.degreeZeroEquiv (Fin (k + 1)) ℂ).symm c)) = c
    have hz : fromZeroRingHom (homogeneousSubmodule (Fin (k + 1)) ℂ) (.powers (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1)) (X i)))
        ((ProjectiveSpace.degreeZeroEquiv (Fin (k + 1)) ℂ).symm c) =
        Away.mk (homogeneousSubmodule (Fin (k + 1)) ℂ)
          ((s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))).map_mem (isHomogeneous_X _ i))
          0 (C c) (by simp only [smul_eq_mul, zero_mul]; exact isHomogeneous_C (Fin (k + 1)) c) := by
      apply HomogeneousLocalization.val_injective
      rfl
    rw [hz, s2e_complexPolynomialChartEvaluation_mk (hp := by simpa using isHomogeneous_C (Fin (k + 1)) c)]
    simp only [eval_C, pow_zero, mul_one]
  · simp only [Category.assoc]
    rw [s2_polynomialProjectiveSpaceIso_snd]
    rw [Proj.awayι_comp_map (hs := isHomogeneous_X (ULift ℤ) i), ← Category.assoc, ← Spec.map_comp]
    rw [vectorToProjectiveSpace_toProj,
      chartIntegralProj_eq_chartIntegralProjAt v _ i hi]
    unfold chartIntegralProjAt
    congr 2
    apply CommRingCat.hom_ext
    exact s2e_complexPolynomialChartEvaluation_integral v i hi

end HodgeLean.Foundations.Program
