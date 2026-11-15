import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionFourFormula
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveAddDegreeOne

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The degree-two addition pullback has its two pure and two mixed bidegree terms. -/
theorem s4_selected_curve_add_cup_bidegrees
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (v w : HQ A 1) :
    homPullback (s4_selected_curve_add_map A Y f) 2 ((cupProductOf A).cup rfl v w) =
      s4_selected_cross_two A Y ⟨2, by decide⟩ ((cupProductOf A).cup rfl v w) (unitClass Y) +
      s4_selected_cross_two A Y ⟨1, by decide⟩ v (homPullback f 1 w) -
      s4_selected_cross_two A Y ⟨1, by decide⟩ w (homPullback f 1 v) +
      s4_selected_cross_two A Y ⟨0, by decide⟩ (unitClass A)
        ((cupProductOf Y).cup rfl (homPullback f 1 v) (homPullback f 1 w)) := by
  have hp : s4_selected_cross_two A Y ⟨2, by decide⟩
      ((cupProductOf A).cup rfl v w) (unitClass Y) =
      homPullback (fst A Y) 2 ((cupProductOf A).cup rfl v w) := by
    change (cupProductOf (A ⊗ Y)).cup rfl _ (homPullback (snd A Y) 0 (unitClass Y)) = _
    have hu : homPullback (snd A Y) 0 (unitClass Y) = unitClass (A ⊗ Y) := by
      simpa only [cupUnit] using spec_homPullback_unit (snd A Y)
    rw [hu, (cupProductOf (A ⊗ Y)).cup_one]
  have hq : s4_selected_cross_two A Y ⟨0, by decide⟩ (unitClass A)
      ((cupProductOf Y).cup rfl (homPullback f 1 v) (homPullback f 1 w)) =
      homPullback (snd A Y) 2
        ((cupProductOf Y).cup rfl (homPullback f 1 v) (homPullback f 1 w)) := by
    change (cupProductOf (A ⊗ Y)).cup rfl (homPullback (fst A Y) 0 (unitClass A)) _ = _
    have hu : homPullback (fst A Y) 0 (unitClass A) = unitClass (A ⊗ Y) := by
      simpa only [cupUnit] using spec_homPullback_unit (fst A Y)
    rw [hu, (cupProductOf (A ⊗ Y)).one_cup]
    rfl
  rw [hp, hq]
  have h := s4_selected_curve_mixed_divisor_cup A Y f v w
  unfold s4_selected_curve_mixed_divisor at h
  rw [spec_homPullback_cup f] at h
  change _ - _ - _ = s4_selected_cross_two A Y ⟨1, by decide⟩ v (homPullback f 1 w) -
    s4_selected_cross_two A Y ⟨1, by decide⟩ w (homPullback f 1 v) at h
  have he := sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp h)
  exact he.trans (by abel)

#print axioms s4_selected_curve_add_cup_bidegrees
end HodgeLean.Foundations.Program
