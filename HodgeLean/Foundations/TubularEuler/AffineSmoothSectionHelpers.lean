import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Smooth affine section algebras and their original scalar maps

The structural algebra maps are those supplied by the specified schemes over
Spec of the complex numbers. HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
attribute [local instance] overSpecAlgebra

theorem smoothAffineSections (X : Over (Spec (CommRingCat.of ℂ))) [Smooth X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U) : Algebra.Smooth ℂ Γ(X.left, U) := by
  rw [← RingHom.smooth_algebraMap]
  exact RingHom.Smooth.propertyIsLocal.respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv
    (X.hom.smooth_appLE (isAffineOpen_top _) hU (by simp))

theorem affineSectionMap_scalarTower
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) (U : X.left.Opens) :
    letI : Algebra Γ(X.left, U) Γ(Y.left, j.left ⁻¹ᵁ U) := (j.left.app U).hom.toAlgebra
    IsScalarTower ℂ Γ(X.left, U) Γ(Y.left, j.left ⁻¹ᵁ U) := by
  letI : Algebra Γ(X.left, U) Γ(Y.left, j.left ⁻¹ᵁ U) := (j.left.app U).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  have h := Scheme.Hom.appLE_comp_appLE j.left X.hom ⊤ U (j.left ⁻¹ᵁ U)
    (by simp) le_rfl
  rw [Over.w j] at h
  rw [Scheme.Hom.appLE_eq_app] at h
  apply RingHom.ext
  intro c
  exact (congrArg (fun f : Γ(Spec (CommRingCat.of ℂ), ⊤) ⟶ Γ(Y.left, j.left ⁻¹ᵁ U) =>
    f ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) h).symm

#print axioms affineSectionMap_scalarTower

#print axioms smoothAffineSections

end HodgeLean.Foundations.TubularEuler
