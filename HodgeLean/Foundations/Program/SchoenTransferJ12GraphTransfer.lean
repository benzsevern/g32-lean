import HodgeLean.Foundations.Program.SchoenTransferJ12GraphCupSpan
import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionSpan

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory TopologicalSpace
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- Transfer defined by the actual difference shear, a target point class, and source fibre trace.
Source: Fulton, Intersection Theory, §16.1, the graph construction for a correspondence action. -/
def s4_selected_graph_transfer
    (A Y : Over (Spec ↧ℂ)) [GrpObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (e : ComplexPoint A) (hec : Order.coheight e.underlying = a)
    (f : Y ⟶ A) (n m : ℕ) (h : 2 * a + n = 2 * d + m) :
    HQ Y n →ₗ[ℚ] HQ A m :=
  (s4_selected_projection A Y d m I).comp
    ((HQ.castEquiv (A ⊗ Y) h).toLinearMap.comp
      (((cupProductOf (A ⊗ Y)).cup rfl
        (homPullback ((s4_selected_graph_shear A Y f).hom ≫ fst A Y) (2 * a)
          (cycleComponentSheafClass A e.underlying hec))).comp
        (homPullback (snd A Y) n)))

/-- The specified graph transfer preserves actual cycle classes in its shifted even degree.
Source: smooth shear transport of external point products and proper projection support purity. -/
theorem s4_selected_graph_transfer_span
    (A Y : Over (Spec ↧ℂ)) [GrpObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d : ℕ) (hA : dim A.left = a) (hY : dim Y.left = d)
    (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (e : ComplexPoint A) (hec : Order.coheight e.underlying = a)
    (f : Y ⟶ A) (p q : ℕ) (h : 2 * a + 2 * p = 2 * d + 2 * q)
    (b : HQ Y (2 * p)) (hb : b ∈ cfd_cycleSpan Y p) :
    s4_selected_graph_transfer A Y a d I e hec f (2 * p) (2 * q) h b ∈
      cfd_cycleSpan A q := by
  have hc := s4_selected_graph_cup_span A Y a hA e hec f p b hb
  have hp := s4_selected_projection_span A Y d (a + p) q hY I
    (by omega : 2 * (a + p) = 2 * d + 2 * q) (Submodule.mem_map_of_mem hc)
  simpa only [s4_selected_graph_transfer, LinearMap.comp_apply, LinearEquiv.coe_coe,
    CupProduct.castEquiv_cup] using hp

#print axioms s4_selected_graph_transfer_span
end HodgeLean.Foundations.Program
