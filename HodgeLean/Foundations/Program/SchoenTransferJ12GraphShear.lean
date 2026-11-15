import HodgeLean.Foundations.Program.CycleFoundationsShear

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
namespace HodgeLean.Foundations.Program

/-- Subtract the given map from the target coordinate, keeping the source coordinate fixed.
Source: the group shear isomorphism over the source. -/
def s4_selected_graph_shear
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] (f : Y ⟶ A) : A ⊗ Y ≅ A ⊗ Y :=
  (β_ A Y) ≪≫ (cfd_shear f).symm ≪≫ (β_ Y A)

/-- The target-first graph shear fixes the source projection.
Source: the defining product projections of the actual group shear. -/
theorem s4_selected_graph_shear_snd
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] (f : Y ⟶ A) :
    (s4_selected_graph_shear A Y f).hom ≫ snd A Y = snd A Y := by
  simp [s4_selected_graph_shear, cfd_shear, Category.assoc]

#print axioms s4_selected_graph_shear_snd
end HodgeLean.Foundations.Program
