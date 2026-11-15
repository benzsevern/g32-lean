import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Surjectivity of retained transitions from their generic squares -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A transition between proper and separated complex bases is surjective
when its specified generic square has dominant target map. -/
theorem s2e_c1_transition_surjective_of_generic_square
    {T S : Scheme} (X Y : Over S)
    [IsProper X.hom] [IsSeparated Y.hom]
    (b : X ⟶ Y) (f : T ⟶ X.left) (g : T ⟶ Y.left)
    [IsDominant g] (hfg : f ≫ b.left = g) : Surjective b.left := by
  haveI : IsDominant (f ≫ b.left) := by rw [hfg]; infer_instance
  haveI : IsDominant b.left := IsDominant.of_comp f b.left
  haveI : IsProper (b.left ≫ Y.hom) := by rw [Over.w b]; infer_instance
  haveI : IsProper b.left := IsProper.of_comp b.left Y.hom
  exact surjective_of_isDominant_of_isClosed_range b.left b.left.isClosedMap.isClosed_range

end HodgeLean.Foundations.Program
