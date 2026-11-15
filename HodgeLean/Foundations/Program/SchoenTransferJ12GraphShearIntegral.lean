import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionFubini
import HodgeLean.Foundations.Program.SchoenTransferJ12ShearProjection
import HodgeLean.Foundations.Program.SchoenTransferJ12GraphShear

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The actual difference shear preserves the normalized top integral on the product.
Source: the two fibre trace orders and invariance under source-dependent abelian translations. -/
theorem s4_selected_graph_shear_top_integral
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d : ℕ) (hA : TopologicalSpace.dim A.left = a) (hY : TopologicalSpace.dim Y.left = d)
    (IA : HQ A (2 * a) ≃ₗ[ℚ] ℚ) (IY : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (f : Y ⟶ A) (x : HQ (A ⊗ Y) (2 * a + 2 * d)) :
    IA (s4_selected_projection A Y d (2 * a) IY
      (HQ.castEquiv (A ⊗ Y) (Nat.add_comm (2 * a) (2 * d))
        (homPullback (s4_selected_graph_shear A Y f).hom (2 * a + 2 * d) x))) =
    IA (s4_selected_projection A Y d (2 * a) IY
      (HQ.castEquiv (A ⊗ Y) (Nat.add_comm (2 * a) (2 * d)) x)) := by
  have hcomm : (β_ Y A).hom ≫ (s4_selected_graph_shear A Y f).hom =
      (cfd_shear f).inv ≫ (β_ Y A).hom := by
    simp [s4_selected_graph_shear, Category.assoc]
  have hinv : (cfd_shear f).inv = (cfd_shear f⁻¹).hom := by
    simp [cfd_shear, GrpObj.comp_inv]
  have hpb : homPullback (β_ Y A).hom (2 * a + 2 * d)
      (homPullback (s4_selected_graph_shear A Y f).hom (2 * a + 2 * d) x) =
      homPullback (cfd_shear f⁻¹).hom (2 * a + 2 * d)
        (homPullback (β_ Y A).hom (2 * a + 2 * d) x) := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, hcomm, hinv,
      spec_homPullback_comp, LinearMap.comp_apply]
  rw [s4_selected_projection_fubini A Y a d hA hY IA IY,
    s4_selected_projection_fubini A Y a d hA hY IA IY, hpb,
    s4_selected_shear_projection A Y a hA IA f⁻¹ (2 * d)]

#print axioms s4_selected_graph_shear_top_integral
end HodgeLean.Foundations.Program
