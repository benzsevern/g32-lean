import HodgeLean.Foundations.Program.SchoenTowerI1bBranchSupport

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A proper dominant complex scheme morphism reaches every actual complex point of its base. -/
theorem proper_dominant_complex_points_surjective
    {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] [IsDominant f.left] :
    Function.Surjective (Point.map f) := by
  intro y
  apply s2v_point_lift_of_mem_proper_image f y
  change y.left (IsLocalRing.closedPoint ℂ) ∈ (f.left.ker.support : Set Y.left)
  rw [Scheme.Hom.support_ker, f.left.denseRange.closure_range]
  trivial

end AlgebraicGeometry.RamifiedNormalization.StageFour
