import HodgeLean.Foundations.Program.SchoenSelectedGeometryAffineAnalytic
import HodgeLean.Foundations.Program.SchoenSelectedGeometrySphere

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ComplexProjectiveSpace AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The standard affine-line map into either projective-line chart.
Source: Hartshorne, Algebraic Geometry, II.2.5, normalized homogeneous coordinates. -/
def s0_projective_line_affine_chart (i : Fin 2) :
    Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)) := by
  let R := MvPolynomial (Fin 1) ℂ
  let w : Fin 2 → R := fun j ↦ if j = i then 1 else MvPolynomial.X 0
  let a : ULift.{0} ℤ →+* R :=
    (Int.castRingHom R).comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom
  let h := s0_projective_chart_eval i a w (by simp [w])
  let q := (AffineSpace.SpecIso (Fin 1) ↧ℂ).hom ≫
    Spec.map (CommRingCat.ofHom h) ≫
    Proj.awayι (UniversalGrading.{0} 1) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X _ i) zero_lt_one
  exact Over.homMk (pullback.lift (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ) q
    (Subsingleton.elim _ _)) (pullback.lift_fst _ _ _)

#print axioms s0_projective_line_affine_chart

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_projective_line_affine_chart_holomorphic (i : Fin 2) :
    letI : SmoothOfRelativeDimension 1
        (Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ)).hom :=
      AffineSpace.smoothOfRelativeDimension_of_card_eq _ (by simp)
    letI : SmoothOfRelativeDimension 1
        (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))).hom :=
      s0_complex_projective_relative_dimension 1
    ContMDiff 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω
      (fun v ↦ Point.map (s0_projective_line_affine_chart i)
        ((affineSpaceEquiv (Fin 1)).symm v)) := by
  letI : SmoothOfRelativeDimension 1 (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ) :=
    AffineSpace.smoothOfRelativeDimension_of_card_eq _ (by simp)
  letI : SmoothOfRelativeDimension 1
      (Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ)).hom := inferInstanceAs
    (SmoothOfRelativeDimension 1 (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ))
  letI : SmoothOfRelativeDimension 1
      (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))).hom :=
    s0_complex_projective_relative_dimension 1
  exact (HodgeLean.Adapters.spec_contMDiff_pointMap_aux _ _ 1 1
    (s0_projective_line_affine_chart i)).comp (s0_affine_coordinate_inverse_holomorphic 1 1)

#print axioms s0_projective_line_affine_chart_holomorphic

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_projective_line_affine_chart_value (i : Fin 2) (v : Fin 1 → ℂ) :
    Point.map (s0_projective_line_affine_chart i) ((affineSpaceEquiv (Fin 1)).symm v) =
      vectorToComplexPoint (fun j : Fin 2 ↦ if j = i then 1 else v 0)
        (by intro h; have hh := congrFun h i; simpa using hh) := by
  let R := MvPolynomial (Fin 1) ℂ
  let w : Fin 2 → R := fun j ↦ if j = i then 1 else MvPolynomial.X 0
  let a : ULift.{0} ℤ →+* R :=
    (Int.castRingHom R).comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom
  let u : CoordinateSpace 1 := fun j ↦ if j = i then 1 else v 0
  have hui : u i = 1 := by simp [u]
  have hi : u i ≠ 0 := by rw [hui]; exact one_ne_zero
  have hu : u ≠ 0 := by intro h; exact hi (congrFun h i)
  have he : (MvPolynomial.eval v).comp (s0_projective_chart_eval i a w (by simp [w])) =
      awayCoordinateEvaluation u i hi := by
    apply awayRingHom_ext i
    · intro b
      exact DFunLike.congr_fun (degreeZero_ringHom_unique
        (((MvPolynomial.eval v).comp (s0_projective_chart_eval i a w (by simp [w]))).comp
          (HomogeneousLocalization.fromZeroRingHom (UniversalGrading 1)
            (Submonoid.powers (MvPolynomial.X i : UniversalRing 1))))
        ((awayCoordinateEvaluation u i hi).comp
          (HomogeneousLocalization.fromZeroRingHom (UniversalGrading 1)
            (Submonoid.powers (MvPolynomial.X i : UniversalRing 1))))) b
    · intro j
      change (MvPolynomial.eval v) (s0_projective_chart_eval i a w (by simp [w])
        (chartCoordinate i j)) = _
      rw [s0_projective_chart_eval_coordinate]
      change (MvPolynomial.eval v) (w j) =
        awayCoordinateEvaluation u i hi
          (HomogeneousLocalization.Away.mk (UniversalGrading 1)
            (MvPolynomial.isHomogeneous_X _ i) 1 (MvPolynomial.X j) _)
      rw [awayCoordinateEvaluation_mk (hr := MvPolynomial.isHomogeneous_X _ j),
        coordinateEvaluationHom_X, hui]
      by_cases hj : j = i <;> simp [w, u, hj]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (((affineSpaceEquiv (Fin 1)).symm v).left ≫
        (s0_projective_line_affine_chart i).left) ≫ pullback.fst _ _ = _
    simp only [s0_projective_line_affine_chart, Over.homMk, Over.Hom.left,
      CostructuredArrow.homMk, Category.assoc (obj := Scheme.{0}),
      pullback.lift_fst, vectorToComplexPoint, vectorToProjectiveSpace, Over.homMk]
    have hb := Over.w ((affineSpaceEquiv (Fin 1)).symm v)
    change ((affineSpaceEquiv (Fin 1)).symm v).left ≫
      (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ) = 𝟙 _ at hb
    exact hb
  · change (((affineSpaceEquiv (Fin 1)).symm v).left ≫
        (s0_projective_line_affine_chart i).left) ≫ pullback.snd _ _ = _
    simp only [s0_projective_line_affine_chart, Over.homMk, Over.Hom.left,
      CostructuredArrow.homMk, Category.assoc (obj := Scheme.{0}),
      pullback.lift_snd, vectorToComplexPoint, vectorToProjectiveSpace, Over.homMk]
    simp only [← Category.assoc (obj := Scheme.{0})]
    rw [s0_affine_coordinate_spec_point, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((MvPolynomial.eval v).comp (s0_projective_chart_eval i a w (by simp [w])))) ≫
      Proj.awayι (UniversalGrading 1) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X _ i) zero_lt_one = chartIntegralProj u hu
    rw [he]
    exact (chartIntegralProj_eq_chartIntegralProjAt u hu i hi).symm

#print axioms s0_projective_line_affine_chart_value

end HodgeLean.Foundations.Program
