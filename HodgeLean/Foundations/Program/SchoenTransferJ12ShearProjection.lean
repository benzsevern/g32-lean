import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionTopCoefficient
import HodgeLean.Foundations.Program.SchoenTransferJ12ProjectionLowerCup
import HodgeLean.Foundations.Program.SchoenTransferJ12PointTranslation
import HodgeLean.Foundations.Program.CycleFoundationsShear

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct DirectSum CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection s4_e1_binaryDegreeEquiv

/-- Translation of the abelian fibre by an actual source-dependent map preserves its fibre trace.
Source: Künneth, the degree-zero trace coordinate and invariance under actual point translations. -/
theorem s4_selected_shear_projection
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d : ℕ) (hA : TopologicalSpace.dim A.left = d)
    (I : HQ A (2 * d) ≃ₗ[ℚ] ℚ) (f : Y ⟶ A)
    (n : ℕ) (x : HQ (Y ⊗ A) (2 * d + n)) :
    s4_selected_projection Y A d n I
      (homPullback (cfd_shear f).hom (2 * d + n) x) =
      s4_selected_projection Y A d n I x := by
  classical
  letI := connectedSpace_complexPoint Y
  let p : ComplexPoint Y := Classical.choice inferInstance
  let σ := cfd_shear f
  let c : A ⟶ Y := (Over.homMk A.hom : A ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ p
  have hfst : σ.hom ≫ fst Y A = fst Y A := by simp [σ, cfd_shear]
  have hcomp : lift c (𝟙 A) ≫ (σ.hom ≫ snd Y A) =
      ((Over.homMk A.hom : A ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ Point.map f p) * 𝟙 A := by
    simp [σ, c, cfd_shear, MonObj.comp_mul, Category.assoc, Point.map]
  let L := (s4_selected_projection Y A d n I).comp (homPullback σ.hom (2 * d + n))
  let R := s4_selected_projection Y A d n I
  let E := s4_e1_binaryDegreeEquiv Y A (2 * d + n)
  have hLR : L.comp E.toLinearMap = R.comp E.toLinearMap := by
    apply DirectSum.linearMap_ext ℚ
    intro k
    apply TensorProduct.ext'
    intro u v
    change L (s4_e1_binaryDegreeEquiv Y A (2 * d + n) (DirectSum.lof ℚ _ _ k (u ⊗ₜ[ℚ] v))) =
      R (s4_e1_binaryDegreeEquiv Y A (2 * d + n) (DirectSum.lof ℚ _ _ k (u ⊗ₜ[ℚ] v)))
    rw [s4_e1_binaryDegreeEquiv_tmul]
    rcases k with ⟨⟨s, t⟩, hst⟩
    change s4_selected_projection Y A d n I
      (homPullback σ.hom (2 * d + n) ((cupProductOf (Y ⊗ A)).cup hst
        (homPullback (fst Y A) s u) (homPullback (snd Y A) t v))) =
      s4_selected_projection Y A d n I ((cupProductOf (Y ⊗ A)).cup hst
        (homPullback (fst Y A) s u) (homPullback (snd Y A) t v))
    rw [spec_homPullback_cup]
    have hbase : homPullback σ.hom s (homPullback (fst Y A) s u) = homPullback (fst Y A) s u := by
      rw [← LinearMap.comp_apply, ← spec_homPullback_comp, hfst]
    have hfibre : homPullback σ.hom t (homPullback (snd Y A) t v) =
        homPullback (σ.hom ≫ snd Y A) t v := by rw [spec_homPullback_comp, LinearMap.comp_apply]
    rw [hbase, hfibre]
    by_cases ht : t ≤ 2 * d
    · by_cases heq : t = 2 * d
      · subst t
        have hs : s = n := by omega
        subst s
        have heval : homPullback (lift c (𝟙 A)) (2 * d)
            (homPullback (σ.hom ≫ snd Y A) (2 * d) v) = v := by
          rw [← LinearMap.comp_apply, ← spec_homPullback_comp, hcomp,
            s4_selected_point_translation_pullback A (Point.map f p) (2 * d), LinearMap.id_apply]
        rw [s4_selected_projection_top_coefficient Y A d n I p, heval,
          s4_selected_projection_even_cross Y A d n I]
      · rw [s4_selected_projection_lower_cup Y A d n s t hst (by omega) I,
          s4_selected_projection_base_off_degree Y A d n s t hst I heq]
    · have hv : v = 0 := by
        letI : SmoothOfRelativeDimension d A.hom := by
          have h := SmoothOfRelativeDimension.of_isIntegral (f := A.hom)
          rwa [hA] at h
        letI := j5d_subsingleton_HQ_of_lt A d (m := t) (by omega)
        exact Subsingleton.elim _ _
      rw [hv]
      simp only [map_zero]
  obtain ⟨z, rfl⟩ := E.surjective x
  exact LinearMap.congr_fun hLR z

#print axioms s4_selected_shear_projection
end HodgeLean.Foundations.Program
