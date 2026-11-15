import HodgeLean.Foundations.Program.SchoenCycleCoordinateImageIdeal
import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s2e_projective_reindex_over {ι κ : Type} (e : ι ≃ κ) :
    Nonempty (Over.mk (ProjectiveSpace.toBase ι (Spec ↧ℂ)) ≅
      Over.mk (ProjectiveSpace.toBase κ (Spec ↧ℂ))) := by
  obtain ⟨E⟩ := HodgeLean.Foundations.spec_g3c_nonempty_proj_iso_of_equiv_aux e
  haveI : IsIso (s2e_projectiveBaseChange E.hom) :=
    (s2e_projectiveBaseChange_isPullback E.hom).isIso_snd_of_isIso
  exact ⟨Over.isoMk (asIso (s2e_projectiveBaseChange E.hom))
    (pullback.lift_fst _ _ _)⟩

theorem s2e_coordinate_intersection_over (k : ℕ) (T : Finset (Fin (k + 1)))
    (hT : T.card ≤ k) :
    Nonempty (s2c_subscheme
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
      (s2e_s2b_intersectionIdeal k T) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (k - T.card + 1)) (Spec ↧ℂ))) := by
  classical
  obtain ⟨e⟩ := s2e_retainedCoordinate_equiv k T hT
  obtain ⟨E⟩ := s2e_projective_reindex_over e
  let f := s2e_coordinateSubspaceInclusion k T
  letI : IsClosedImmersion f := s2e_coordinateSubspaceInclusion_isClosedImmersion k T
  have hk : f.ker = s2e_s2b_intersectionIdeal k T :=
    s2e_coordinateSubspaceInclusion_kernel k T hT
  have hf : f ≫ ProjectiveSpace.toBase _ (Spec ↧ℂ) =
      ProjectiveSpace.toBase _ (Spec ↧ℂ) := pullback.lift_fst _ _ _
  let F : Over.mk (ProjectiveSpace.toBase {j : Fin (k + 1) // j ∉ T} (Spec ↧ℂ)) ≅
      s2c_subscheme (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) f.ker :=
    Over.isoMk (asIso f.toImage) (by
      change f.toImage ≫ (f.imageι ≫ ProjectiveSpace.toBase _ _) = _
      rw [← Category.assoc, Scheme.Hom.toImage_imageι]
      exact hf)
  have hi : s2c_subscheme (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
      f.ker = s2c_subscheme (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
      (s2e_s2b_intersectionIdeal k T) := congrArg _ hk
  exact ⟨(eqToIso hi).symm ≪≫ F.symm ≪≫ E⟩

end HodgeLean.Foundations.Program
