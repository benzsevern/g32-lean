import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionFormula

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The actual product top coordinate from fibre contraction and the specified two factor coordinates.
Source: field-coefficient Künneth and evaluation on the two top cohomology factors. -/
def s4_selected_product_integral
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d : ℕ) (IA : HQ A (2 * a) ≃ₗ[ℚ] ℚ) (IY : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) :
    HQ (A ⊗ Y) (2 * a + 2 * d) →ₗ[ℚ] ℚ :=
  IA.toLinearMap.comp ((s4_selected_projection A Y d (2 * a) IY).comp
    (HQ.castEquiv (A ⊗ Y) (Nat.add_comm (2 * a) (2 * d))).toLinearMap)

/-- Pairing a fibre projection with a base class is the specified product top coordinate of their cup.
Source: the actual projection formula and transport along the stated degree equality. -/
theorem s4_selected_product_integral_base_cup
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d i j : ℕ) (h : i + j = 2 * a)
    (IA : HQ A (2 * a) ≃ₗ[ℚ] ℚ) (IY : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (u : HQ A i) (v : HQ (A ⊗ Y) (2 * d + j)) :
    s4_selected_product_integral A Y a d IA IY
      ((cupProductOf (A ⊗ Y)).cup (by omega : i + (2 * d + j) = 2 * a + 2 * d)
        (homPullback (fst A Y) i u) v) =
      IA ((cupProductOf A).cup h u (s4_selected_projection A Y d j IY v)) := by
  have hp (k : ℕ) (hk : i + j = k) :
      s4_selected_projection A Y d k IY
        ((cupProductOf (A ⊗ Y)).cup (by omega : i + (2 * d + j) = 2 * d + k)
          (homPullback (fst A Y) i u) v) =
      (cupProductOf A).cup hk u (s4_selected_projection A Y d j IY v) := by
    subst k
    exact s4_selected_projection_formula A Y d i j IY u v
  unfold s4_selected_product_integral
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [CupProduct.castEquiv_cup]
  exact congrArg IA (hp (2 * a) h)

#print axioms s4_selected_product_integral_base_cup
end HodgeLean.Foundations.Program
