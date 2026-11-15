import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionZeroCoordinate

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

/-- A top-total-degree fibre coefficient is evaluated on an actual base point before a base cup.
Source: the projection formula and the degree-zero fibre trace coordinate calculation. -/
theorem s4_selected_projection_top_coefficient
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d n : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (e : ComplexPoint A)
    (a : HQ A n) (b : HQ (A ⊗ Y) (2 * d)) :
    s4_selected_projection A Y d n I
      ((cupProductOf (A ⊗ Y)).cup (Nat.add_comm n (2 * d))
        (homPullback (fst A Y) n a) b) =
      I (homPullback (lift
        ((Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e) (𝟙 Y)) (2 * d) b) • a := by
  have h := s4_selected_projection_formula A Y d n 0 I a b
  simp only [Nat.add_zero] at h
  erw [s4_selected_projection_zero_coordinate A Y d I e b] at h
  have hunit : (cupProductOf A).cup rfl a (cupUnit A) = a := (cupProductOf A).cup_one a
  apply h.trans
  change (cupProductOf A).cup (Nat.add_zero n) a
    (I (homPullback (lift
      ((Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e) (𝟙 Y)) (2 * d) b) • cupUnit A) = _
  rw [map_smul]
  exact congrArg (fun z : HQ A n =>
    I (homPullback (lift
      ((Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e) (𝟙 Y)) (2 * d) b) • z) hunit

#print axioms s4_selected_projection_top_coefficient
end HodgeLean.Foundations.Program
