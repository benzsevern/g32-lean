import HodgeLean.Foundations.Program.SchoenCycleBranchImagePoints

/-! Actual complex point lifts for proper dominant scheme maps. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_proper_dominant_point_surjective
    {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    (f : X ⟶ Y) [IsProper f.left] [IsDominant f.left] :
    Function.Surjective (Point.map f) := by
  haveI : Surjective f.left :=
    surjective_of_isDominant_of_isClosed_range f.left f.left.isClosedMap.isClosed_range
  intro y
  exact s2e_complexPoint_lift_of_mem_range f y (f.left.surjective y.underlying)

end HodgeLean.Foundations.QuotientDuality
