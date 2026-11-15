import HodgeLean.Foundations.Program.SchoenTransferJ12PointConstant
import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionFormula

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection
  s4_e1_binaryDegreeEquiv

/-- The degree-zero fibre trace is its scalar obtained on any actual base point section.
Source: field-coefficient Künneth and vanishing of positive-degree pullback through a point. -/
theorem s4_selected_projection_zero_coordinate
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (e : ComplexPoint A)
    (b : HQ (A ⊗ Y) (2 * d)) :
    s4_selected_projection A Y d 0 I b =
      I (homPullback (lift
        ((Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e) (𝟙 Y)) (2 * d) b) • cupUnit A := by
  classical
  let c : Y ⟶ A := (Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e
  let s : Y ⟶ A ⊗ Y := lift c (𝟙 Y)
  let L := s4_selected_projection A Y d 0 I
  let R := LinearMap.smulRight (I.toLinearMap.comp (homPullback s (2 * d))) (cupUnit A)
  let E := s4_e1_binaryDegreeEquiv A Y (2 * d)
  have hLR : L.comp E.toLinearMap = R.comp E.toLinearMap := by
    apply DirectSum.linearMap_ext ℚ
    intro k
    apply TensorProduct.ext'
    intro a b
    change L (s4_e1_binaryDegreeEquiv A Y (2 * d) (DirectSum.lof ℚ _ _ k (a ⊗ₜ[ℚ] b))) =
      R (s4_e1_binaryDegreeEquiv A Y (2 * d) (DirectSum.lof ℚ _ _ k (a ⊗ₜ[ℚ] b)))
    rw [s4_e1_binaryDegreeEquiv_tmul]
    rcases k with ⟨⟨u, v⟩, huv⟩
    change s4_selected_projection A Y d 0 I ((cupProductOf (A ⊗ Y)).cup huv
      (homPullback (fst A Y) u a) (homPullback (snd A Y) v b)) =
      I (homPullback s (2 * d) ((cupProductOf (A ⊗ Y)).cup huv
        (homPullback (fst A Y) u a) (homPullback (snd A Y) v b))) • cupUnit A
    have hf : homPullback s u (homPullback (fst A Y) u a) = homPullback c u a := by
      rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_fst]
    have hs : homPullback s v (homPullback (snd A Y) v b) = b := by
      rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_snd,
        spec_homPullback_id, LinearMap.id_apply]
    rw [spec_homPullback_cup, hf, hs]
    by_cases hu : u = 0
    · subst u
      have hv : v = 2 * d := by omega
      subst v
      obtain ⟨r, rfl⟩ := (cupProductOf_zeroEquiv A).surjective a
      have hp : s4_selected_projection A Y d 0 I ((cupProductOf (A ⊗ Y)).cup huv
          (homPullback (fst A Y) 0 (cupProductOf_zeroEquiv A r))
          (homPullback (snd A Y) (2 * d) b)) = I b • cupProductOf_zeroEquiv A r := by
        simpa only [Nat.add_zero] using
          s4_selected_projection_even_cross A Y d 0 I (cupProductOf_zeroEquiv A r) b
      rw [hp]
      have hunit : (cupProductOf Y).cup huv (cupUnit Y) b = b := (cupProductOf Y).one_cup b
      simp only [cupProductOf_zeroEquiv_apply, map_smul, spec_homPullback_unit,
        LinearMap.smul_apply, hunit, smul_smul, smul_eq_mul]
      rw [mul_comm]
    · have hp : s4_selected_projection A Y d 0 I ((cupProductOf (A ⊗ Y)).cup huv
          (homPullback (fst A Y) u a) (homPullback (snd A Y) v b)) = 0 := by
        simpa only [Nat.add_zero] using
          s4_selected_projection_base_off_degree A Y d 0 u v (by omega) I (by omega) a b
      rw [hp]
      rw [s4_selected_point_constant_pullback_positive A Y e u hu]
      simp only [LinearMap.zero_apply, map_zero, zero_smul]
  obtain ⟨z, rfl⟩ := E.surjective b
  exact LinearMap.congr_fun hLR z

#print axioms s4_selected_projection_zero_coordinate
end HodgeLean.Foundations.Program
