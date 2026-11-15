import HodgeLean.Foundations.Program.SchoenTransferJ12GraphTransfer
import HodgeLean.Foundations.Program.SchoenTransferJ12ProductIntegral
import HodgeLean.Foundations.Program.SchoenTransferE1CupElementary

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The specified graph transfer pairing is its actual graph-normal product top integral.
Source: the general projection formula and the actual degree transport in the graph transfer. -/
theorem s4_selected_graph_transfer_base_pairing
    (A Y : Over (Spec ↧ℂ)) [GrpObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d p q s : ℕ) (hshift : a + p = d + s) (hpair : q + s = a)
    (IA : HQ A (2 * a) ≃ₗ[ℚ] ℚ) (IY : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (e : ComplexPoint A) (hec : Order.coheight e.underlying = a)
    (f : Y ⟶ A) (w : HQ A (2 * q)) (b : HQ Y (2 * p)) :
    IA ((cupProductOf A).cup (by omega : 2 * q + 2 * s = 2 * a) w
      (s4_selected_graph_transfer A Y a d IY e hec f (2 * p) (2 * s) (by omega) b)) =
    s4_selected_product_integral A Y a d IA IY
      ((cupProductOf (A ⊗ Y)).cup (by omega : 2 * q + (2 * a + 2 * p) = 2 * a + 2 * d)
        (homPullback (fst A Y) (2 * q) w)
        ((cupProductOf (A ⊗ Y)).cup rfl
          (homPullback ((s4_selected_graph_shear A Y f).hom ≫ fst A Y) (2 * a)
            (cycleComponentSheafClass A e.underlying hec))
          (homPullback (snd A Y) (2 * p) b))) := by
  let z := (cupProductOf (A ⊗ Y)).cup rfl
    (homPullback ((s4_selected_graph_shear A Y f).hom ≫ fst A Y) (2 * a)
      (cycleComponentSheafClass A e.underlying hec))
    (homPullback (snd A Y) (2 * p) b)
  change IA ((cupProductOf A).cup (by omega : 2 * q + 2 * s = 2 * a) w
    (s4_selected_projection A Y d (2 * s) IY
      (HQ.castEquiv (A ⊗ Y) (by omega : 2 * a + 2 * p = 2 * d + 2 * s) z))) =
    s4_selected_product_integral A Y a d IA IY
      ((cupProductOf (A ⊗ Y)).cup (by omega : 2 * q + (2 * a + 2 * p) = 2 * a + 2 * d)
        (homPullback (fst A Y) (2 * q) w) z)
  symm
  rw [s4_e1_cup_cast_right (A ⊗ Y) (by omega : 2 * a + 2 * p = 2 * d + 2 * s)
    (by omega) (by omega) (homPullback (fst A Y) (2 * q) w) z]
  exact s4_selected_product_integral_base_cup A Y a d (2 * q) (2 * s) (by omega) IA IY w _

#print axioms s4_selected_graph_transfer_base_pairing
end HodgeLean.Foundations.Program
