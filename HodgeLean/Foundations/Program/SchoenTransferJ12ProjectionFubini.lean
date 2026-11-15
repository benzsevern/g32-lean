import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionFormula
import HodgeLean.RealDefs.TopDegreeRank

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
attribute [local irreducible] cupProductOf homPullback s4_selected_projection s4_e1_binaryDegreeEquiv

/-- The two normalized top fibre traces agree after the actual product symmetry and degree transport.
Source: field-coefficient Künneth, dimension vanishing and Fubini for external top classes. -/
theorem s4_selected_projection_fubini
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a d : ℕ) (hA : TopologicalSpace.dim A.left = a) (hY : TopologicalSpace.dim Y.left = d)
    (IA : HQ A (2 * a) ≃ₗ[ℚ] ℚ) (IY : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (x : HQ (A ⊗ Y) (2 * a + 2 * d)) :
    IA (s4_selected_projection A Y d (2 * a) IY
      (HQ.castEquiv (A ⊗ Y) (Nat.add_comm (2 * a) (2 * d)) x)) =
    IY (s4_selected_projection Y A a (2 * d) IA
      (homPullback (β_ Y A).hom (2 * a + 2 * d) x)) := by
  classical
  let L := IA.toLinearMap.comp ((s4_selected_projection A Y d (2 * a) IY).comp
    (HQ.castEquiv (A ⊗ Y) (Nat.add_comm (2 * a) (2 * d))).toLinearMap)
  let R := IY.toLinearMap.comp ((s4_selected_projection Y A a (2 * d) IA).comp
    (homPullback (β_ Y A).hom (2 * a + 2 * d)))
  let E := s4_e1_binaryDegreeEquiv A Y (2 * a + 2 * d)
  have hLR : L.comp E.toLinearMap = R.comp E.toLinearMap := by
    apply DirectSum.linearMap_ext ℚ
    intro k
    apply TensorProduct.ext'
    intro u v
    change L (s4_e1_binaryDegreeEquiv A Y (2 * a + 2 * d) (DirectSum.lof ℚ _ _ k (u ⊗ₜ[ℚ] v))) =
      R (s4_e1_binaryDegreeEquiv A Y (2 * a + 2 * d) (DirectSum.lof ℚ _ _ k (u ⊗ₜ[ℚ] v)))
    rw [s4_e1_binaryDegreeEquiv_tmul]
    rcases k with ⟨⟨s, t⟩, hst⟩
    change IA (s4_selected_projection A Y d (2 * a) IY
      (HQ.castEquiv (A ⊗ Y) (Nat.add_comm (2 * a) (2 * d))
        ((cupProductOf (A ⊗ Y)).cup hst
          (homPullback (fst A Y) s u) (homPullback (snd A Y) t v)))) =
      IY (s4_selected_projection Y A a (2 * d) IA
        (homPullback (β_ Y A).hom (2 * a + 2 * d)
          ((cupProductOf (A ⊗ Y)).cup hst
            (homPullback (fst A Y) s u) (homPullback (snd A Y) t v))))
    rw [CupProduct.castEquiv_cup, spec_homPullback_cup]
    have hf : homPullback (β_ Y A).hom s (homPullback (fst A Y) s u) =
        homPullback (snd Y A) s u := by
      rw [← LinearMap.comp_apply, ← spec_homPullback_comp]
      simp
    have hs : homPullback (β_ Y A).hom t (homPullback (snd A Y) t v) =
        homPullback (fst Y A) t v := by
      rw [← LinearMap.comp_apply, ← spec_homPullback_comp]
      simp
    rw [hf, hs]
    by_cases heq : t = 2 * d
    · subst t
      have hs' : s = 2 * a := by omega
      subst s
      rw [s4_selected_projection_even_cross A Y d (2 * a) IY,
        s4_selected_projection_fibre_cross Y A a (2 * d) IA]
      simp only [map_smul, smul_eq_mul]
      exact mul_comm _ _
    · by_cases ht : t ≤ 2 * d
      · have hu : u = 0 := by
          letI : SmoothOfRelativeDimension a A.hom := by
            have h := SmoothOfRelativeDimension.of_isIntegral (f := A.hom)
            rwa [hA] at h
          letI := j5d_subsingleton_HQ_of_lt A a (m := s) (by omega)
          exact Subsingleton.elim _ _
        rw [hu]
        simp only [map_zero, LinearMap.zero_apply]
      · have hv : v = 0 := by
          letI : SmoothOfRelativeDimension d Y.hom := by
            have h := SmoothOfRelativeDimension.of_isIntegral (f := Y.hom)
            rwa [hY] at h
          letI := j5d_subsingleton_HQ_of_lt Y d (m := t) (by omega)
          exact Subsingleton.elim _ _
        rw [hv]
        simp only [map_zero]
  obtain ⟨z, rfl⟩ := E.surjective x
  exact LinearMap.congr_fun hLR z

#print axioms s4_selected_projection_fubini
end HodgeLean.Foundations.Program
