import HodgeLean.Foundations.Program.SchoenTowerComplexPointStabilizers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Topology

namespace HodgeLean.Foundations.Program

/-- A nonempty finite-type complex scheme has an actual complex point. -/
theorem s2t_nonempty_complexPoints (X : Over (Spec ↧ℂ)) [Nonempty X.left]
    [LocallyOfFiniteType X.hom] : Nonempty (ComplexPoint X) := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints (Set.univ_nonempty :
    (Set.univ : Set X.left).Nonempty) isOpen_univ.isLocallyClosed
  exact ⟨Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)⟩

end HodgeLean.Foundations.Program
