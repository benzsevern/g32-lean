import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionFourProducts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- An external degree-two class with its base degree explicitly indexed. -/
def s4_selected_cross_two
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (i : Fin 3) (a : HQ A i.val) (b : HQ Y (2 - i.val)) : HQ (A ⊗ Y) 2 :=
  (cupProductOf (A ⊗ Y)).cup (by have := i.isLt; omega)
    (homPullback (fst A Y) i.val a) (homPullback (snd A Y) (2 - i.val) b)

/-- Products of degree-two external classes project to zero unless their base degrees sum to two. -/
theorem s4_selected_projection_four_bidegrees_zero
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (i k : Fin 3) (hik : i.val + k.val ≠ 2)
    (a : HQ A i.val) (b : HQ Y (2 - i.val))
    (c : HQ A k.val) (d : HQ Y (2 - k.val)) :
    s4_selected_projection A Y 1 2 I
      ((cupProductOf (A ⊗ Y)).cup rfl
        (s4_selected_cross_two A Y i a b) (s4_selected_cross_two A Y k c d)) = 0 := by
  let r := (2 - i.val) + (2 - k.val)
  have hi := i.isLt
  have hk := k.isLt
  have hr : r < 5 := by dsimp only [r]; omega
  have hr2 : r ≠ 2 := by dsimp only [r]; omega
  unfold s4_selected_cross_two
  rw [s4_cup_middle_exchange (A ⊗ Y) (cupProductOf (A ⊗ Y))
    i.val (2 - i.val) k.val (2 - k.val) 2 2 (4 - r) r 4
    (by omega) (by omega) (by dsimp only [r]; omega) rfl rfl,
    map_smul, ← spec_homPullback_cup, ← spec_homPullback_cup]
  have hz : s4_selected_projection A Y 1 2 I
      ((cupProductOf (A ⊗ Y)).cup (show (4 - r) + r = 4 by omega)
        (homPullback (fst A Y) (4 - r) ((cupProductOf A).cup (by dsimp only [r]; omega) a c))
        (homPullback (snd A Y) r ((cupProductOf Y).cup rfl b d))) = 0 := by
    rw [(cupProductOf (A ⊗ Y)).graded_comm (i := r) (j := 4 - r)
      (by omega) (by omega)
      (homPullback (snd A Y) r ((cupProductOf Y).cup rfl b d))
      (homPullback (fst A Y) (4 - r) ((cupProductOf A).cup (by dsimp only [r]; omega) a c)),
      map_smul]
    rw [s4_selected_projection_four_off_degree A Y I ⟨r, hr⟩ hr2, smul_zero]
  rw [hz, smul_zero]

/-- Matching external bidegrees project by their fibre pairing with the exact Koszul sign. -/
theorem s4_selected_projection_four_bidegrees_pair
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (i k : Fin 3) (hik : i.val + k.val = 2)
    (a : HQ A i.val) (b : HQ Y (2 - i.val))
    (c : HQ A k.val) (d : HQ Y (2 - k.val)) :
    s4_selected_projection A Y 1 2 I
      ((cupProductOf (A ⊗ Y)).cup rfl
        (s4_selected_cross_two A Y i a b) (s4_selected_cross_two A Y k c d)) =
      ((-1 : ℚ) ^ ((2 - i.val) * k.val)) •
        (I ((cupProductOf Y).cup (by have := i.isLt; have := k.isLt; omega) b d) •
          (cupProductOf A).cup hik a c) := by
  have hi := i.isLt
  have hk := k.isLt
  unfold s4_selected_cross_two
  rw [s4_cup_middle_exchange (A ⊗ Y) (cupProductOf (A ⊗ Y))
    i.val (2 - i.val) k.val (2 - k.val) 2 2 2 2 4
    (by omega) (by omega) hik (by omega) rfl,
    map_smul, ← spec_homPullback_cup, ← spec_homPullback_cup,
    s4_selected_projection_even_cross A Y 1 2 I]

#print axioms s4_selected_projection_four_bidegrees_pair

#print axioms s4_selected_projection_four_bidegrees_zero
end HodgeLean.Foundations.Program
