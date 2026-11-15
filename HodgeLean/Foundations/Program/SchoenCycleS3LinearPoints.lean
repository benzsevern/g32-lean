import HodgeLean.Foundations.Program.SchoenCycleS3PolynomialPoints
import HodgeLean.Foundations.Program.SchoenCycleS3LinearOver
import HodgeLean.Foundations.Program.SchoenCycleS3IdealIsoTransport

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- A homogeneous polynomial belongs to the evaluation point exactly when its value vanishes. -/
theorem s2e_polynomial_chart_point_mem {k d : ℕ} (v : CoordinateSpace k)
    (i : Fin (k + 1)) (hi : v i ≠ 0)
    (p : MvPolynomial (Fin (k + 1)) ℂ) (hp : p.IsHomogeneous d) (hd : 0 < d) :
    p ∈ (Proj.awayι (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)
      (isHomogeneous_X _ i) zero_lt_one
      ((Spec.map (CommRingCat.ofHom (s2e_complexPolynomialChartEvaluation v (X i)
        (by simpa only [eval_X] using hi)))) (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal ↔
      eval v p = 0 := by
  rw [← not_iff_not]
  change ((Spec.map (CommRingCat.ofHom (s2e_complexPolynomialChartEvaluation v (X i)
    (by simpa only [eval_X] using hi)))) (IsLocalRing.closedPoint ℂ) ∈
      (Proj.awayι (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)
        (isHomogeneous_X _ i) zero_lt_one) ⁻¹ᵁ Proj.basicOpen _ p) ↔ _
  rw [Proj.awayι_preimage_basicOpen (𝒜 := homogeneousSubmodule (Fin (k + 1)) ℂ)
    (isHomogeneous_X ℂ i) zero_lt_one hp hd]
  change (s2e_complexPolynomialChartEvaluation v (X i) (by simpa only [eval_X] using hi)
    (Away.isLocalizationElem (isHomogeneous_X ℂ i) hp) ∉
      (IsLocalRing.closedPoint ℂ).asIdeal) ↔ _
  have he : Away.isLocalizationElem (isHomogeneous_X ℂ i) hp =
      Away.mk (homogeneousSubmodule (Fin (k + 1)) ℂ) (isHomogeneous_X ℂ i) d p
        (by simpa using hp) := by
    apply HomogeneousLocalization.val_injective
    simp [Away.isLocalizationElem]
  rw [he, s2e_complexPolynomialChartEvaluation_mk (hp := by simpa using hp)]
  simp [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot, hi]

/-- The polynomial point corresponding to a nonzero homogeneous vector. -/
def s2e_polynomialEvaluationPoint {k : ℕ} (v : CoordinateSpace k) (hv : v ≠ 0) :
    Proj (homogeneousSubmodule (Fin (k + 1)) ℂ) :=
  (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).inv
    (vectorToComplexPoint v hv).underlying

/-- The polynomial point is represented by evaluation in any nonvanishing coordinate chart. -/
theorem s2e_polynomialEvaluationPoint_chart {k : ℕ} (v : CoordinateSpace k) (hv : v ≠ 0)
    (i : Fin (k + 1)) (hi : v i ≠ 0) :
    s2e_polynomialEvaluationPoint v hv =
      Proj.awayι (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)
        (isHomogeneous_X _ i) zero_lt_one
        ((Spec.map (CommRingCat.ofHom (s2e_complexPolynomialChartEvaluation v (X i)
          (by simpa only [eval_X] using hi)))) (IsLocalRing.closedPoint ℂ)) := by
  have h := s2e_complexPolynomialChartEvaluation_point v i hi
  let F (f : MvPolynomial (Fin (k + 1)) ℂ) (hf : eval v f ≠ 0)
      (hfdeg : f ∈ homogeneousSubmodule (Fin (k + 1)) ℂ 1) :=
    Spec.map (CommRingCat.ofHom (s2e_complexPolynomialChartEvaluation v f hf)) ≫
      Proj.awayι (homogeneousSubmodule (Fin (k + 1)) ℂ) f hfdeg zero_lt_one
  have heq (f g : MvPolynomial (Fin (k + 1)) ℂ) (hf : eval v f ≠ 0)
      (hg : eval v g ≠ 0) (hfd : f ∈ homogeneousSubmodule (Fin (k + 1)) ℂ 1)
      (hgd : g ∈ homogeneousSubmodule (Fin (k + 1)) ℂ 1) (hfg : f = g) :
      F f hf hfd = F g hg hgd := by
    subst g
    rfl
  have hmap := heq _ (X i) (by
      change eval v (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1)) (X i)) ≠ 0
      rw [s2_polynomialIntegralCoordinates_X, eval_X]
      exact hi) (by simpa only [eval_X] using hi)
    ((s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))).map_mem (isHomogeneous_X _ i))
    (isHomogeneous_X ℂ i) (s2_polynomialIntegralCoordinates_X ℂ (Fin (k + 1)) i)
  change F _ _ _ = F _ _ _ at hmap
  rw [← Category.assoc] at h
  change F _ _ _ ≫ _ = _ at h
  erw [hmap] at h
  have hh := congrArg (fun f => f (IsLocalRing.closedPoint ℂ)) h
  have hhh := congrArg (fun x => (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).inv x) hh
  simp only [← Scheme.Hom.comp_apply, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] at hhh
  convert hhh.symm using 1
  · rfl
  · rfl

/-- Every homogeneous degree is detected by polynomial evaluation at the specified point. -/
theorem s2e_polynomialEvaluationPoint_mem {k d : ℕ} (v : CoordinateSpace k) (hv : v ≠ 0)
    (p : MvPolynomial (Fin (k + 1)) ℂ) (hp : p.IsHomogeneous d) :
    p ∈ (s2e_polynomialEvaluationPoint v hv).asHomogeneousIdeal ↔ eval v p = 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero v hv
  rw [s2e_polynomialEvaluationPoint_chart v hv i hi]
  have hX := s2e_polynomial_chart_point_mem v i hi (X i) (isHomogeneous_X ℂ i) zero_lt_one
  have hXi : (X i : MvPolynomial (Fin (k + 1)) ℂ) ∉
      (Proj.awayι (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)
        (isHomogeneous_X _ i) zero_lt_one
        ((Spec.map (CommRingCat.ofHom (s2e_complexPolynomialChartEvaluation v (X i)
          (by simpa only [eval_X] using hi)))) (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal := by
    simpa only [hX, eval_X] using hi
  have hh := s2e_polynomial_chart_point_mem v i hi (p * X i)
    (hp.mul (isHomogeneous_X ℂ i)) (by omega)
  have hh' : p * X i ∈
      (Proj.awayι (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)
        (isHomogeneous_X _ i) zero_lt_one
        ((Spec.map (CommRingCat.ofHom (s2e_complexPolynomialChartEvaluation v (X i)
          (by simpa only [eval_X] using hi)))) (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal ↔
      eval v p = 0 := by
    simpa only [map_mul, eval_X, mul_eq_zero, or_iff_left hi] using hh
  constructor
  · intro hm
    exact hh'.mp (Ideal.mul_mem_right _ _ hm)
  · intro hm
    exact ((inferInstance : Ideal.IsPrime _).mem_or_mem (hh'.mpr hm)).resolve_right hXi

/-- Linear substitution carries an evaluation point to evaluation at the transformed vector. -/
theorem s2e_linearProjIso_evaluationPoint {k : ℕ}
    (e : CoordinateSpace k ≃ₗ[ℂ] CoordinateSpace k) (v : CoordinateSpace k) (hv : v ≠ 0) :
    (s2e_linearProjIso e).hom (s2e_polynomialEvaluationPoint v hv) =
      s2e_polynomialEvaluationPoint (e v) (e.map_ne_zero_iff.mpr hv) := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d p hp
  change s2e_gradedLinearSubstitution e p ∈ (s2e_polynomialEvaluationPoint v hv).asHomogeneousIdeal ↔ _
  erw [s2e_polynomialEvaluationPoint_mem v hv _ ((s2e_gradedLinearSubstitution e).map_mem hp),
    s2e_polynomialEvaluationPoint_mem (e v) (e.map_ne_zero_iff.mpr hv) p hp]
  change eval v (s2e_linearSubstitution e.toLinearMap p) = 0 ↔ _
  rw [s2e_linearSubstitution_eval]
  rfl

/-- The scheme automorphism over the complex base has the prescribed linear point action. -/
theorem s2e_linearProjectiveOverIso_point {k : ℕ}
    (e : CoordinateSpace k ≃ₗ[ℂ] CoordinateSpace k) (v : CoordinateSpace k) (hv : v ≠ 0) :
    (s2e_linearProjectiveOverIso e).hom.left (vectorToComplexPoint v hv).underlying =
      (vectorToComplexPoint (e v) (e.map_ne_zero_iff.mpr hv)).underlying := by
  change (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom
    ((s2e_linearProjIso e).hom (s2e_polynomialEvaluationPoint v hv)) = _
  rw [s2e_linearProjIso_evaluationPoint]
  exact (Scheme.homeoOfIso (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1)))).apply_symm_apply _

end HodgeLean.Foundations.Program
