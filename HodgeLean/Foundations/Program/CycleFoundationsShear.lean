import HodgeLean.Foundations.Program.CycleFoundationsDefs

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

/-- The group shear attached to a morphism into a group object. -/
def cfd_shear {A B : Over (Spec ↧ℂ)} [GrpObj A] (f : B ⟶ A) :
    B ⊗ A ≅ B ⊗ A where
  hom := lift (fst B A) ((fst B A ≫ f) * snd B A)
  inv := lift (fst B A) ((fst B A ≫ f)⁻¹ * snd B A)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]

/-- The second component of the shear is smooth over a smooth base. -/
theorem cfd_shear_smooth {A B : Over (Spec ↧ℂ)} [GrpObj A]
    [Smooth B.hom] (f : B ⟶ A) :
    Smooth (((cfd_shear f).hom ≫ snd B A).left) := by
  letI : IsIso (cfd_shear f).hom.left := inferInstance
  letI : Smooth (snd B A).left := by
    change Smooth (Limits.pullback.snd B.hom A.hom)
    infer_instance
  change Smooth ((cfd_shear f).hom.left ≫ (snd B A).left)
  infer_instance

end HodgeLean.Foundations.Program
