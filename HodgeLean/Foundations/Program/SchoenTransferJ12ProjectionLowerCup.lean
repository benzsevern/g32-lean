import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionFormula

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

/-- A base class cannot make a lower-total-degree product class reach the required fibre degree.
Source: the finite-fibre Künneth direct sum and the projection formula on external cups. -/
theorem s4_selected_projection_lower_cup
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d n i j : ℕ) (h : i + j = 2 * d + n) (hj : j < 2 * d)
    (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) (a : HQ A i) (b : HQ (A ⊗ Y) j) :
    s4_selected_projection A Y d n I
      ((cupProductOf (A ⊗ Y)).cup h (homPullback (fst A Y) i a) b) = 0 := by
  classical
  let L := (s4_selected_projection A Y d n I).comp
    ((cupProductOf (A ⊗ Y)).cup h (homPullback (fst A Y) i a))
  let E := s4_e1_binaryDegreeEquiv A Y j
  have hL : L.comp E.toLinearMap = 0 := by
    apply DirectSum.linearMap_ext ℚ
    intro k
    apply TensorProduct.ext'
    intro u v
    change L (s4_e1_binaryDegreeEquiv A Y j (DirectSum.lof ℚ _ _ k (u ⊗ₜ[ℚ] v))) = 0
    rw [s4_e1_binaryDegreeEquiv_tmul]
    rcases k with ⟨⟨s, t⟩, hst⟩
    change s4_selected_projection A Y d n I
      ((cupProductOf (A ⊗ Y)).cup h (homPullback (fst A Y) i a)
        ((cupProductOf (A ⊗ Y)).cup hst
          (homPullback (fst A Y) s u) (homPullback (snd A Y) t v))) = 0
    rw [← (cupProductOf (A ⊗ Y)).assoc rfl hst (by omega) h,
      ← spec_homPullback_cup (fst A Y) rfl]
    exact s4_selected_projection_base_off_degree A Y d n (i + s) t (by omega) I (by omega) _ v
  obtain ⟨z, rfl⟩ := E.surjective b
  exact LinearMap.congr_fun hL z

#print axioms s4_selected_projection_lower_cup
end HodgeLean.Foundations.Program
