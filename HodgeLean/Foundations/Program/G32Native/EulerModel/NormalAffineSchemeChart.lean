import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalProjectiveScheme
import HodgeLean.Foundations.Program.SchoenSelectedGeometryLineCharts

/-! # The actual affine scheme map for the specified normal base chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
open scoped Manifold ContDiff
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual scheme morphism with ordered homogeneous coordinates `(1,z)`. -/
def normalAffineSchemeChart (k : ℕ) :
    Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) := by
  let R := MvPolynomial (Fin k) ℂ
  let w : Fin (k + 1) → R := Fin.cons 1 MvPolynomial.X
  let a : ULift.{0} ℤ →+* R :=
    (Int.castRingHom R).comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom
  let h := s0_projective_chart_eval (0 : Fin (k + 1)) a w rfl
  let q := (AffineSpace.SpecIso (Fin k) ↧ℂ).hom ≫
    Spec.map (CommRingCat.ofHom h) ≫
    Proj.awayι (UniversalGrading.{0} k) (MvPolynomial.X (0 : Fin (k + 1)))
      (MvPolynomial.isHomogeneous_X _ _) zero_lt_one
  exact Over.homMk (pullback.lift (complexAffineSpace (Fin k) ↘ Spec ↧ℂ) q
    (Subsingleton.elim _ _)) (pullback.lift_fst _ _ _)

#print axioms normalAffineSchemeChart
/-- The actual affine scheme chart evaluates to the specified ordered homogeneous vector. -/
theorem normalAffineSchemeChart_value (k : ℕ) (v : Fin k → ℂ) :
    Point.map (normalAffineSchemeChart k) ((affineSpaceEquiv (Fin k)).symm v) =
      vectorToComplexPoint (Fin.cons (1 : ℂ) v)
        (by intro h; exact one_ne_zero (congrFun h 0)) := by
  let i : Fin (k + 1) := 0
  let R := MvPolynomial (Fin k) ℂ
  let w : Fin (k + 1) → R := Fin.cons 1 MvPolynomial.X
  let a : ULift.{0} ℤ →+* R :=
    (Int.castRingHom R).comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom
  let u : CoordinateSpace k := Fin.cons 1 v
  have hui : u i = 1 := by rfl
  have hi : u i ≠ 0 := by rw [hui]; exact one_ne_zero
  have hu : u ≠ 0 := by intro h; exact hi (congrFun h i)
  have he : (MvPolynomial.eval v).comp (s0_projective_chart_eval i a w (by rfl)) =
      awayCoordinateEvaluation u i hi := by
    apply awayRingHom_ext i
    · intro b
      exact DFunLike.congr_fun (degreeZero_ringHom_unique
        (((MvPolynomial.eval v).comp (s0_projective_chart_eval i a w (by rfl))).comp
          (HomogeneousLocalization.fromZeroRingHom (UniversalGrading k)
            (Submonoid.powers (MvPolynomial.X i : UniversalRing k))))
        ((awayCoordinateEvaluation u i hi).comp
          (HomogeneousLocalization.fromZeroRingHom (UniversalGrading k)
            (Submonoid.powers (MvPolynomial.X i : UniversalRing k))))) b
    · intro j
      change (MvPolynomial.eval v) (s0_projective_chart_eval i a w (by rfl)
        (chartCoordinate i j)) = _
      rw [s0_projective_chart_eval_coordinate]
      change (MvPolynomial.eval v) (w j) =
        awayCoordinateEvaluation u i hi
          (HomogeneousLocalization.Away.mk (UniversalGrading k)
            (MvPolynomial.isHomogeneous_X _ i) 1 (MvPolynomial.X j) _)
      rw [awayCoordinateEvaluation_mk (hr := MvPolynomial.isHomogeneous_X _ j),
        coordinateEvaluationHom_X, hui]
      refine Fin.cases ?_ (fun t => ?_) j
      · simp [w, u, i]
      · simp [w, u, i]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (((affineSpaceEquiv (Fin k)).symm v).left ≫
        (normalAffineSchemeChart k).left) ≫ pullback.fst _ _ = _
    simp only [normalAffineSchemeChart, Over.homMk, Over.Hom.left,
      CostructuredArrow.homMk, Category.assoc (obj := Scheme.{0}),
      pullback.lift_fst, vectorToComplexPoint, vectorToProjectiveSpace, Over.homMk]
    have hb := Over.w ((affineSpaceEquiv (Fin k)).symm v)
    change ((affineSpaceEquiv (Fin k)).symm v).left ≫
      (complexAffineSpace (Fin k) ↘ Spec ↧ℂ) = 𝟙 _ at hb
    exact hb
  · change (((affineSpaceEquiv (Fin k)).symm v).left ≫
        (normalAffineSchemeChart k).left) ≫ pullback.snd _ _ = _
    simp only [normalAffineSchemeChart, Over.homMk, Over.Hom.left,
      CostructuredArrow.homMk, Category.assoc (obj := Scheme.{0}),
      pullback.lift_snd, vectorToComplexPoint, vectorToProjectiveSpace, Over.homMk]
    simp only [← Category.assoc (obj := Scheme.{0})]
    rw [s0_affine_coordinate_spec_point, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((MvPolynomial.eval v).comp (s0_projective_chart_eval i a w (by rfl)))) ≫
      Proj.awayι (UniversalGrading k) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X _ i) zero_lt_one = chartIntegralProj u hu
    rw [he]
    exact (chartIntegralProj_eq_chartIntegralProjAt u hu i hi).symm


#print axioms normalAffineSchemeChart_value
/-- The specified normal base chart is holomorphic for the actual native scheme manifold structures. -/
theorem normalAffineSchemeChart_holomorphic (k : ℕ) :
    letI : SmoothOfRelativeDimension k
      (Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ)).hom :=
        AffineSpace.smoothOfRelativeDimension_of_card_eq _ (by simp)
    letI : SmoothOfRelativeDimension k
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom :=
        s0_complex_projective_relative_dimension k
    ContMDiff 𝓘(ℂ, Fin k → ℂ) 𝓘(ℂ, Fin k → ℂ) ω
      (fun v => Point.map (normalAffineSchemeChart k)
        ((affineSpaceEquiv (Fin k)).symm v)) := by
  letI : SmoothOfRelativeDimension k (complexAffineSpace (Fin k) ↘ Spec ↧ℂ) :=
    AffineSpace.smoothOfRelativeDimension_of_card_eq _ (by simp)
  letI : SmoothOfRelativeDimension k
      (Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ)).hom := inferInstanceAs
    (SmoothOfRelativeDimension k (complexAffineSpace (Fin k) ↘ Spec ↧ℂ))
  letI : SmoothOfRelativeDimension k
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom :=
    s0_complex_projective_relative_dimension k
  exact (HodgeLean.Adapters.spec_contMDiff_pointMap_aux _ _ k k
    (normalAffineSchemeChart k)).comp (s0_affine_coordinate_inverse_holomorphic k k)

#print axioms normalAffineSchemeChart_holomorphic
end HodgeLean.Foundations.Program.G32Native.EulerModel
