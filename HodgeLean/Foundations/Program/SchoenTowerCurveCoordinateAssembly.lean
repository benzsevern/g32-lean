import HodgeLean.Foundations.Program.SchoenTowerPrincipalCoordinates
import HodgeLean.Foundations.Program.SchoenAffineCoefficientMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint

namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra s2t_complexStalkAlgebra

/-- The global sections of a finite-type affine complex scheme form a finitely generated
complex algebra with their structure-map algebra structure.
Source: Mathlib, `LocallyOfFiniteType`; `s2_affineCoefficientMap_finiteType`. -/
theorem s2t_globalSections_finiteType (X : Over (Spec ↧ℂ)) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] : Algebra.FiniteType ℂ Γ(X.left, ⊤) := by
  apply RingHom.finiteType_algebraMap.mp
  have h : algebraMap ℂ Γ(X.left, ⊤) = s2_affineCoefficientMap X.left X.hom := by
    ext c
    change X.hom.appLE ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso ↧ℂ).inv c) =
      X.hom.appTop ((Scheme.ΓSpecIso ↧ℂ).inv c)
    simp only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl, op_id]
    rw [X.left.presheaf.map_id, Category.comp_id]
  rw [h]
  exact s2_affineCoefficientMap_finiteType X.left X.hom

end HodgeLean.Foundations.Program
