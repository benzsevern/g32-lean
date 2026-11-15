import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateInclusionPoints

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Coordinate restriction preserves the specified coefficient morphism. -/
theorem paired_c3_coordinate_inclusion_toBase {k n : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) :
    ((s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).inv ≫
      pairedC3PolynomialCoordinateInclusion (A := ℂ) e ≫
      (s2_polynomialProjectiveSpaceIso ℂ (Fin (n + 1))).hom) ≫
        ProjectiveSpace.toBase _ (Spec ↧ℂ) = ProjectiveSpace.toBase _ (Spec ↧ℂ) := by
  let c := (ProjectiveSpace.degreeZeroEquiv (Fin (k + 1)) ℂ).symm.toRingHom.comp
    (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) ℂ).toRingHom
  have hc : ∀ a : homogeneousSubmodule (Fin (n + 1)) ℂ 0,
      (c a : MvPolynomial (Fin (k + 1)) ℂ) = pairedC3GradedCoordinateProjection e a := by
    intro a
    have ha := congrArg Subtype.val
      ((ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) ℂ).symm_apply_apply a)
    change C ((ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) ℂ) a) = _
    rw [← ha]
    change _ = killCompl e.injective (C _)
    rw [killCompl_C]
  have hb := s2_projMap_toSpecZero _ _ (pairedC3GradedCoordinateProjection (A := ℂ) e)
    (s2e_irrelevant_le_map_of_graded_retraction _ _
      (pairedC3GradedCoordinateProjection e) (pairedC3GradedCoordinateSection e)
      (paired_c3_graded_coordinate_retraction e)) c hc
  change pairedC3PolynomialCoordinateInclusion (A := ℂ) e ≫ _ = _ at hb
  simp only [Category.assoc, s2_polynomialProjectiveSpaceIso_toBase]
  rw [← Category.assoc (pairedC3PolynomialCoordinateInclusion (A := ℂ) e), hb]
  rw [Category.assoc, ← Spec.map_comp]
  have hh : (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) ℂ).symm.toCommRingCatIso.hom ≫
      (CommRingCat.ofHom c) =
      (ProjectiveSpace.degreeZeroEquiv (Fin (k + 1)) ℂ).symm.toCommRingCatIso.hom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact congrArg (ProjectiveSpace.degreeZeroEquiv (Fin (k + 1)) ℂ).symm
      ((ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) ℂ).apply_symm_apply a)
  rw [hh, ← s2_polynomialProjectiveSpaceIso_toBase, Iso.inv_hom_id_assoc]

/-- The original point morphism is retained under coordinate extension. -/
theorem paired_c3_coordinate_inclusion_point_morphism {k n : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (u : Fin (k + 1) → ℂ) (hu : u ≠ 0) :
    (vectorToComplexPoint u hu).left ≫
      ((s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).inv ≫
        pairedC3PolynomialCoordinateInclusion (A := ℂ) e ≫
        (s2_polynomialProjectiveSpaceIso ℂ (Fin (n + 1))).hom) =
      (vectorToComplexPoint (pairedC3CoordinateVectorLift e u)
        (fun hz => hu ((paired_c3_coordinate_vector_lift_injective e)
          (hz.trans (map_zero (pairedC3CoordinateVectorLift e)).symm)))).left := by
  let f : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)) := Over.homMk _ (paired_c3_coordinate_inclusion_toBase e)
  exact congrArg (fun p => p.left)
    (ComplexPoint.underlying_injective_of_locallyOfFiniteType
      (X := Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))
      (show (Point.map f (vectorToComplexPoint u hu)).underlying = _ from
        paired_c3_coordinate_inclusion_point e u hu))

#print axioms paired_c3_coordinate_inclusion_toBase
#print axioms paired_c3_coordinate_inclusion_point_morphism
end HodgeLean.Foundations.Program.G32Native
