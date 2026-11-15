import HodgeLean.Foundations.Program.SchoenTransferJ12CorrespondenceTransfer
import HodgeLean.Foundations.Program.SchoenTransferJ12AbelianCorrSpan

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- Kernels pulled back from actual abelian correspondences preserve cycle spans on a general source.
Source: graph transfer composition, proper projection and abelian cycle-class multiplication. -/
theorem s4_selected_pullback_kernel_action_span
    (A B Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (D d : ℕ) (hB : TopologicalSpace.dim B.left = D) (hY : TopologicalSpace.dim Y.left = d)
    (IB : HQ B (2 * D) ≃ₗ[ℚ] ℚ) (IY : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (e : ComplexPoint B) (hec : Order.coheight e.underlying = D)
    (he : IB (cycleComponentSheafClass B e.underlying hec) = 1)
    (g : Y ⟶ B) (c p q s : ℕ) (hshift : D + p = d + s) (hkernel : c + s = D + q)
    (K : HQ (A ⊗ B) (2 * c)) (hK : K ∈ cfd_cycleSpan (A ⊗ B) c)
    (b : HQ Y (2 * p)) (hb : b ∈ cfd_cycleSpan Y p) :
    s4_selected_corr_action A Y d IY c (2 * p) (2 * q) (by omega)
      (homPullback (lift (fst A Y) (snd A Y ≫ g)) (2 * c) K) b ∈ cfd_cycleSpan A q := by
  rw [← s4_selected_correspondence_graph_transfer A B Y D d hB hY IB IY e hec he g c p q s hshift hkernel]
  apply s4_selected_abelian_corr_span A B D hB IB c s q (by omega) K hK
  exact s4_selected_graph_transfer_span B Y D d hB hY IY e hec g p s (by omega) b hb

#print axioms s4_selected_pullback_kernel_action_span
end HodgeLean.Foundations.Program
