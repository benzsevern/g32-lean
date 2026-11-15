import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! The exact mapping-cone criterion for the actual cochain morphism.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A cochain morphism is a quasi-isomorphism precisely when its actual mapping cone is exact.
Source: Mathlib, Algebra.Homology.HomotopyCategory.Acyclic and the distinguished mapping-cone triangle.
HC no distance; AV milestone no distance.
-/
theorem quasiIso_iff_mappingCone_acyclic {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  have h := (HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f) (HomotopyCategory.mappingCone_triangleh_distinguished f)
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).symm.trans h

#print axioms quasiIso_iff_mappingCone_acyclic
end HodgeLean.Foundations.RationalHomologyManifold
