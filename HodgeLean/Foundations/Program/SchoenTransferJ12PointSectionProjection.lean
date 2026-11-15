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

/-- Restriction to an actual point section equals fibre contraction against a normalized top class.
Source: field-coefficient Künneth, the unit in degree zero, and vanishing above the fibre dimension. -/
theorem s4_selected_point_section_projection
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (hA : TopologicalSpace.dim A.left = d)
    (e : ComplexPoint A) (I : HQ A (2 * d) ≃ₗ[ℚ] ℚ)
    (t : HQ A (2 * d)) (ht : I t = 1)
    (n : ℕ) (x : HQ (Y ⊗ A) n) :
    homPullback (lift (𝟙 Y)
      ((Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e)) n x =
    s4_selected_projection Y A d n I
      ((cupProductOf (Y ⊗ A)).cup (Nat.add_comm n (2 * d))
        x (homPullback (snd Y A) (2 * d) t)) := by
  let c : Y ⟶ A := (Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e
  let L := homPullback (lift (𝟙 Y) c) n
  let R := (s4_selected_projection Y A d n I).comp
    (((cupProductOf (Y ⊗ A)).cup (Nat.add_comm n (2 * d))).flip
      (homPullback (snd Y A) (2 * d) t))
  let E := s4_e1_binaryDegreeEquiv Y A n
  have hLR : L.comp E.toLinearMap = R.comp E.toLinearMap := by
    apply DirectSum.linearMap_ext ℚ
    intro k
    apply TensorProduct.ext'
    intro a b
    change L (s4_e1_binaryDegreeEquiv Y A n (DirectSum.lof ℚ _ _ k (a ⊗ₜ[ℚ] b))) =
      R (s4_e1_binaryDegreeEquiv Y A n (DirectSum.lof ℚ _ _ k (a ⊗ₜ[ℚ] b)))
    rw [s4_e1_binaryDegreeEquiv_tmul]
    rcases k with ⟨⟨u, v⟩, huv⟩
    change homPullback (lift (𝟙 Y) c) n
      ((cupProductOf (Y ⊗ A)).cup huv
        (homPullback (fst Y A) u a) (homPullback (snd Y A) v b)) =
      s4_selected_projection Y A d n I ((cupProductOf (Y ⊗ A)).cup (Nat.add_comm n (2 * d))
        ((cupProductOf (Y ⊗ A)).cup huv
          (homPullback (fst Y A) u a) (homPullback (snd Y A) v b))
        (homPullback (snd Y A) (2 * d) t))
    have hf : homPullback (lift (𝟙 Y) c) u (homPullback (fst Y A) u a) = a := by
      rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_fst,
        spec_homPullback_id, LinearMap.id_apply]
    have hs : homPullback (lift (𝟙 Y) c) v (homPullback (snd Y A) v b) =
        homPullback c v b := by
      rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_snd]
    rw [spec_homPullback_cup, hf, hs]
    by_cases hv : v = 0
    · subst v
      have hu : u = n := by omega
      subst u
      obtain ⟨r, rfl⟩ := (cupProductOf_zeroEquiv A).surjective b
      simp only [cupProductOf_zeroEquiv_apply, map_smul, spec_homPullback_unit,
        LinearMap.smul_apply]
      have hYunit : (cupProductOf Y).cup huv a (cupUnit Y) = a := (cupProductOf Y).cup_one a
      have hPunit : (cupProductOf (Y ⊗ A)).cup huv (homPullback (fst Y A) n a)
          (cupUnit (Y ⊗ A)) = homPullback (fst Y A) n a :=
        (cupProductOf (Y ⊗ A)).cup_one _
      rw [hYunit, hPunit, s4_selected_projection_even_cross Y A d n I, ht, one_smul]
    · rw [(cupProductOf (Y ⊗ A)).assoc huv rfl (by omega) (by omega),
        ← spec_homPullback_cup (snd Y A) rfl]
      rw [s4_selected_point_constant_pullback_positive A Y e v hv, LinearMap.zero_apply, map_zero]
      have hz : (cupProductOf A).cup rfl b t = 0 := by
        letI : SmoothOfRelativeDimension d A.hom := by
          have h := SmoothOfRelativeDimension.of_isIntegral (f := A.hom)
          rwa [hA] at h
        letI := j5d_subsingleton_HQ_of_lt A d (m := v + 2 * d) (by omega)
        exact Subsingleton.elim _ _
      rw [hz, map_zero, map_zero, map_zero]
  obtain ⟨z, rfl⟩ := E.surjective x
  exact LinearMap.congr_fun hLR z

#print axioms s4_selected_point_section_projection
end HodgeLean.Foundations.Program
