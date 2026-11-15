import HodgeLean.Foundations.Program.CycleFoundationsShear

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
namespace HodgeLean.Foundations.Program

/-- Addition of an arbitrary curve map to the abelian factor, in target-first order.
Source: Fulton, Intersection Theory, §1.7; the group shear over the curve. -/
def s4_selected_curve_add_map
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] (f : Y ⟶ A) : A ⊗ Y ⟶ A :=
  (β_ A Y).hom ≫ (cfd_shear f).hom ≫ snd Y A

/-- Adding an arbitrary map into a group to the first factor is a smooth morphism.
Source: Hartshorne, Algebraic Geometry, III.10, base change and composition of smooth morphisms. -/
theorem s4_selected_curve_add_smooth
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [Smooth Y.hom] (f : Y ⟶ A) :
    Smooth (s4_selected_curve_add_map A Y f).left := by
  letI : Smooth (((cfd_shear f).hom ≫ snd Y A).left) := cfd_shear_smooth f
  change Smooth ((β_ A Y).hom.left ≫ ((cfd_shear f).hom ≫ snd Y A).left)
  infer_instance

#print axioms s4_selected_curve_add_smooth
end HodgeLean.Foundations.Program
