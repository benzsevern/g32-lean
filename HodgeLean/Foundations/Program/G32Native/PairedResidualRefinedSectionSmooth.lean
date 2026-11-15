import HodgeLean.Foundations.Program.SchoenCycleAffineCoordinateRestriction
import Mathlib.RingTheory.Smooth.StandardSmooth

/-! # Absolute smoothness of the original refined affine section algebra -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Every affine refinement of the original native coordinate neighbourhood
retains its absolute standard smooth dimension with the prescribed scalars.
Source: EGA IV, 17.11.1; Hartshorne, Algebraic Geometry, II.8. -/
theorem residual_refined_section_standardSmooth
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (W : X.left.affineOpens)
    (hW : W.1 ≤ (localEtaleCoordinates X d p).neighborhood) :
    letI := s2e_step1_sectionAlgebra X W.1
    Algebra.IsStandardSmoothOfRelativeDimension d ℂ Γ(X.left, W.1) := by
  let DX := localEtaleCoordinates X d p
  letI := s2e_step1_sectionAlgebra X DX.neighborhood
  letI := s2e_step1_sectionAlgebra X W.1
  let ρ := s2e_sectionRestrictionAlgHom X DX.neighborhood W.1 hW
  let G := ρ.comp DX.coordinateAlgHom
  have hG : G.toRingHom.Etale :=
    RingHom.Etale.stableUnderComposition _ _ DX.etale
      (s2e_affine_section_restriction_etale X ⟨DX.neighborhood, DX.isAffine⟩ W hW)
  let P := MvPolynomial (Fin d) ℂ
  let A := Γ(X.left, W.1)
  letI : Algebra P A := G.toAlgebra
  letI : IsScalarTower ℂ P A := IsScalarTower.of_algebraMap_eq' G.comp_algebraMap.symm
  letI : Algebra.Etale P A := RingHom.etale_algebraMap.mp hG
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 P A :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  simpa only [zero_add] using
    Algebra.IsStandardSmoothOfRelativeDimension.trans d 0 ℂ P A

#print axioms residual_refined_section_standardSmooth
end HodgeLean.Foundations.Program.G32Native
