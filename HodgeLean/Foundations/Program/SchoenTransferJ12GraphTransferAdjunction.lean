import HodgeLean.Foundations.Program.SchoenTransferJ12GraphTransferBasePairing
import HodgeLean.Foundations.Program.SchoenTransferJ12GraphIntegralPairing

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The cycle-preserving graph transfer is adjoint to actual pullback in the indicated even degrees.
Source: the graph normal-class integral calculation and the actual projection formula. -/
theorem s4_selected_graph_transfer_adjunction
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d p q s : ℕ) (hA : TopologicalSpace.dim A.left = a) (hY : TopologicalSpace.dim Y.left = d)
    (hshift : a + p = d + s) (hpair : q + s = a)
    (IA : HQ A (2 * a) ≃ₗ[ℚ] ℚ) (IY : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (e : ComplexPoint A) (hec : Order.coheight e.underlying = a)
    (he : IA (cycleComponentSheafClass A e.underlying hec) = 1)
    (f : Y ⟶ A) (w : HQ A (2 * q)) (b : HQ Y (2 * p)) :
    IA ((cupProductOf A).cup (by omega : 2 * q + 2 * s = 2 * a) w
      (s4_selected_graph_transfer A Y a d IY e hec f (2 * p) (2 * s) (by omega) b)) =
    IY ((cupProductOf Y).cup (by omega : 2 * q + 2 * p = 2 * d)
      (homPullback f (2 * q) w) b) := by
  exact (s4_selected_graph_transfer_base_pairing A Y a d p q s hshift hpair IA IY e hec f w b).trans
    (s4_selected_graph_integral_pairing A Y a d p q hA hY (by omega) IA IY e hec he f w b)

#print axioms s4_selected_graph_transfer_adjunction
end HodgeLean.Foundations.Program
