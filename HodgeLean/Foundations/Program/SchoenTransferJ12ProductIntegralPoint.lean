import HodgeLean.Foundations.Program.SchoenTransferJ12ProductIntegral
import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionFubini
import HodgeLean.Foundations.Program.SchoenTransferJ12PointSectionProjection

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

/-- A normalized target top class evaluates the product integral by restriction to an actual point section.
Source: the two fibre trace orders and the actual point-section projection formula. -/
theorem s4_selected_product_integral_point_cup
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d : ℕ) (hA : TopologicalSpace.dim A.left = a) (hY : TopologicalSpace.dim Y.left = d)
    (IA : HQ A (2 * a) ≃ₗ[ℚ] ℚ) (IY : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (e : ComplexPoint A) (t : HQ A (2 * a)) (ht : IA t = 1)
    (v : HQ (A ⊗ Y) (2 * d)) :
    s4_selected_product_integral A Y a d IA IY
      ((cupProductOf (A ⊗ Y)).cup rfl (homPullback (fst A Y) (2 * a) t) v) =
      IY (homPullback (lift
        ((Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e) (𝟙 Y)) (2 * d) v) := by
  let c : Y ⟶ A := (Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e
  have hfst : homPullback (β_ Y A).hom (2 * a) (homPullback (fst A Y) (2 * a) t) =
      homPullback (snd Y A) (2 * a) t := by
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp]
    simp
  have hcomm : (cupProductOf (Y ⊗ A)).cup rfl
      (homPullback (snd Y A) (2 * a) t) (homPullback (β_ Y A).hom (2 * d) v) =
      (cupProductOf (Y ⊗ A)).cup (Nat.add_comm (2 * d) (2 * a))
        (homPullback (β_ Y A).hom (2 * d) v) (homPullback (snd Y A) (2 * a) t) := by
    have hs : (-1 : ℚ) ^ ((2 * d) * (2 * a)) = 1 := by
      rw [show (2 * d) * (2 * a) = 2 * (d * (2 * a)) by ring, pow_mul]
      norm_num
    have h := (cupProductOf (Y ⊗ A)).graded_comm (Nat.add_comm (2 * d) (2 * a)) rfl
      (homPullback (β_ Y A).hom (2 * d) v) (homPullback (snd Y A) (2 * a) t)
    simpa only [hs, one_smul] using h
  have hmap : lift (𝟙 Y) c ≫ (β_ Y A).hom = lift c (𝟙 Y) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  unfold s4_selected_product_integral
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [s4_selected_projection_fubini A Y a d hA hY IA IY,
    spec_homPullback_cup, hfst, hcomm,
    ← s4_selected_point_section_projection A Y a hA e IA t ht (2 * d),
    ← LinearMap.comp_apply, ← spec_homPullback_comp, hmap]

#print axioms s4_selected_product_integral_point_cup
end HodgeLean.Foundations.Program
