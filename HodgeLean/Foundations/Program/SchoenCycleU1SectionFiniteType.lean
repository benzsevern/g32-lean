import HodgeLean.Foundations.Program.SchoenCycleU1AffineCharts

/-! # Finite-type section algebras on actual affine charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Affine sections carry a finite-type algebra structure from the actual base map.
Source: Mathlib, `Scheme.Hom.finiteType_appLE`; Hartshorne, Algebraic Geometry, II.3. -/
theorem s2e_u1_section_finiteType
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (V : X.left.Opens) (hV : IsAffineOpen V) :
    letI := s2e_step1_sectionAlgebra X V
    Algebra.FiniteType ℂ Γ(X.left, V) := by
  letI := s2e_step1_sectionAlgebra X V
  rw [← RingHom.finiteType_algebraMap]
  change ((X.hom.appLE ⊤ V le_top).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom).FiniteType
  exact (X.hom.finiteType_appLE (isAffineOpen_top _) hV le_top).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).surjective)

end HodgeLean.Foundations.Program
