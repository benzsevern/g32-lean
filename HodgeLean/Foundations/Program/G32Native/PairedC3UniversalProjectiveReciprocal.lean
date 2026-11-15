import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveRestriction
import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveChartOverlap
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-! # Reciprocal projective charts over arbitrary coefficient rings -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- The reciprocal comparison descends from the universal invertible
coordinate. The coefficient ring itself need not be reduced or of finite type. -/
theorem pairedC3_projective_unit_reciprocal
    {C : Type} [CommRing C] [Algebra ℂ C]
    [IsSeparated projectiveLine.hom] [LocallyOfFiniteType projectiveLine.hom]
    (c : Cˣ) : projectiveLineChart 1 (↑c⁻¹ : C) = projectiveLineChart 0 (c : C) := by
  let D := Localization.Away (Polynomial.X : ℂ[X])
  letI : IsDomain D := IsLocalization.Away.isDomain (R := ℂ[X]) D (x := Polynomial.X) Polynomial.X_ne_zero
  letI : LocallyOfFiniteType (ComplexPoint.affineSpecStructureMap D) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  let d : Dˣ := (IsLocalization.Away.algebraMap_isUnit
    (S := D) (Polynomial.X : ℂ[X])).unit
  let e : ℂ[X] →ₐ[ℂ] C := Polynomial.aeval (c : C)
  have he : IsUnit (e Polynomial.X) := by
    simpa only [e, Polynomial.aeval_X] using c.isUnit
  let φ : D →ₐ[ℂ] C := IsLocalization.Away.liftAlgHom Polynomial.X he
  have hdval : (d : D) = algebraMap ℂ[X] D Polynomial.X := IsUnit.unit_spec _
  have hd : φ (d : D) = (c : C) := by
    rw [hdval]
    change IsLocalization.Away.lift (S := D) Polynomial.X he
      (algebraMap ℂ[X] D Polynomial.X) = _
    rw [IsLocalization.Away.lift_eq]
    exact Polynomial.aeval_X _
  have hunit : Units.map φ.toMonoidHom d = c := Units.ext hd
  have hinv : φ (↑d⁻¹ : D) = (↑c⁻¹ : C) := by
    change (↑(Units.map φ.toMonoidHom d)⁻¹ : C) = _
    rw [hunit]
  have hD : projectiveLineChart 1 (↑d⁻¹ : D) = projectiveLineChart 0 (d : D) := by
    simpa only [mul_one] using pairedC3_projective_normalized_overlap d (1 : D) 1 (one_mul 1)
  apply Over.OverMorphism.ext
  have h := congrArg (fun m => Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ m.left) hD
  simpa only [pairedC3_projective_chart_restriction φ, hd, hinv] using h

/-- Ambient reciprocity gives the normalized projective comparison over
any residual coefficient ring. -/
theorem pairedC3_projective_normalized_overlap_universal
    {C : Type} [CommRing C] [Algebra ℂ C]
    [IsSeparated projectiveLine.hom] [LocallyOfFiniteType projectiveLine.hom]
    (c : Cˣ) (s t : C) (hst : s * t = 1) :
    projectiveLineChart 1 ((↑c⁻¹ : C) * t) =
      projectiveLineChart 0 ((c : C) * s) := by
  let d := Units.mkOfMulEqOne ((c : C) * s) ((↑c⁻¹ : C) * t)
    (pairedC3_normalized_overlap c s t hst)
  exact pairedC3_projective_unit_reciprocal d

#print axioms pairedC3_projective_normalized_overlap_universal
#print axioms pairedC3_projective_unit_reciprocal
end HodgeLean.Foundations.Program.G32Native
