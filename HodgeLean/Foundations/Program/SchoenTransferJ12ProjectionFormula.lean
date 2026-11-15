import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionBaseOffDegree
import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionEvenCross
import HodgeLean.Foundations.Program.SchoenTransferE1BinaryCup

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection
  s4_e1_binaryDegreeEquiv

/-- The specified fibre trace satisfies the projection formula for general smooth projective factors.
Source: Hatcher, Algebraic Topology, §3.2, external cups and field-coefficient Künneth. -/
theorem s4_selected_projection_formula
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d i j : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (a : HQ A i) (b : HQ (A ⊗ Y) (2 * d + j)) :
    s4_selected_projection A Y d (i + j) I
      ((cupProductOf (A ⊗ Y)).cup (by omega : i + (2 * d + j) = 2 * d + (i + j))
        (homPullback (fst A Y) i a) b) =
      (cupProductOf A).cup rfl a (s4_selected_projection A Y d j I b) := by
  classical
  let L := (s4_selected_projection A Y d (i + j) I).comp
    ((cupProductOf (A ⊗ Y)).cup (by omega : i + (2 * d + j) = 2 * d + (i + j))
      (homPullback (fst A Y) i a))
  let R := ((cupProductOf A).cup rfl a).comp (s4_selected_projection A Y d j I)
  let E := s4_e1_binaryDegreeEquiv A Y (2 * d + j)
  have hLR : L.comp E.toLinearMap = R.comp E.toLinearMap := by
    apply DirectSum.linearMap_ext ℚ
    intro k
    apply TensorProduct.ext'
    intro u v
    change L (s4_e1_binaryDegreeEquiv A Y (2 * d + j)
      (DirectSum.lof ℚ _ _ k (u ⊗ₜ[ℚ] v))) =
      R (s4_e1_binaryDegreeEquiv A Y (2 * d + j)
        (DirectSum.lof ℚ _ _ k (u ⊗ₜ[ℚ] v)))
    rw [s4_e1_binaryDegreeEquiv_tmul]
    rcases k with ⟨⟨s, t⟩, hst⟩
    change s4_selected_projection A Y d (i + j) I
      ((cupProductOf (A ⊗ Y)).cup (by omega : i + (2 * d + j) = 2 * d + (i + j))
        (homPullback (fst A Y) i a)
        ((cupProductOf (A ⊗ Y)).cup hst
          (homPullback (fst A Y) s u) (homPullback (snd A Y) t v))) =
      (cupProductOf A).cup rfl a
        (s4_selected_projection A Y d j I ((cupProductOf (A ⊗ Y)).cup hst
          (homPullback (fst A Y) s u) (homPullback (snd A Y) t v)))
    rw [← (cupProductOf (A ⊗ Y)).assoc rfl hst (by omega) (by omega),
      ← spec_homPullback_cup (fst A Y) rfl]
    by_cases ht : t = 2 * d
    · subst t
      have hs : s = j := by omega
      subst s
      rw [s4_selected_projection_even_cross A Y d (i + j),
        s4_selected_projection_even_cross A Y d j]
      exact ((cupProductOf A).cup rfl a).map_smul (I v) u |>.symm
    · rw [s4_selected_projection_base_off_degree A Y d (i + j) (i + s) t (by omega) I ht,
        s4_selected_projection_base_off_degree A Y d j s t hst I ht, map_zero]
  obtain ⟨z, rfl⟩ := E.surjective b
  exact LinearMap.congr_fun hLR z

#print axioms s4_selected_projection_formula
end HodgeLean.Foundations.Program
