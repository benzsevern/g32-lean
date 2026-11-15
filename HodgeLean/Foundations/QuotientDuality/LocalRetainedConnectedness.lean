import HodgeLean.Foundations.Connected
import HodgeLean.Foundations.Program.SchoenCycleSymmetricPoints

/-! Connectedness of the actual initial quotient from its supplied power projection. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

theorem initial_quotient_pathConnected (Y W : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (n : ℕ) (q : g3_power Y n ⟶ W) (hq : Function.Surjective (Point.map q)) :
    PathConnectedSpace (ComplexPoint W) := by
  letI := HodgeLean.Foundations.pathConnectedSpace_complexPoint Y
  let e := s2e_projectivePowerPointHomeomorph Y n
  letI : PathConnectedSpace (ComplexPoint (g3_power Y n)) :=
    e.symm.surjective.pathConnectedSpace e.symm.continuous
  exact hq.pathConnectedSpace (Point.continuous_map q)

#print axioms initial_quotient_pathConnected
end HodgeLean.Foundations.QuotientDuality
