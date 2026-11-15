import HodgeLean.Foundations.Program.SchoenCycleC2SmoothConormalFramesHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Smoothness of the ambient scheme only on a neighbourhood of a source
point suffices for the actual local conormal frame at that point. -/
theorem s2e_conormal_frames_of_smooth_ambient_open
    (Q W : Over (Spec ↧ℂ)) (n k : ℕ) [SmoothOfRelativeDimension n Q.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (U : W.left.Opens)
    (hsm : SmoothOfRelativeDimension (n + k) (U.ι ≫ W.hom))
    (x : Q.left) (hx : ι.left x ∈ U) :
    ∃ V : Q.left.Opens, x ∈ V ∧ Nonempty
      (Scheme.Modules.restrict (s2c_conormal ι.left) V.ι ≅
        (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Fin k) : V.toScheme.Modules)) := by
  let P := ι.left ⁻¹ᵁ U
  let Q' : Over (Spec ↧ℂ) := Over.mk (P.ι ≫ Q.hom)
  let W' : Over (Spec ↧ℂ) := Over.mk (U.ι ≫ W.hom)
  let f : Q' ⟶ W' := Over.homMk (ι.left ∣_ U) (by
    change (ι.left ∣_ U) ≫ U.ι ≫ W.hom = P.ι ≫ Q.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w ι])
  letI : SmoothOfRelativeDimension n Q'.hom := by
    change SmoothOfRelativeDimension n (P.ι ≫ Q.hom)
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (P.ι ≫ Q.hom))
  letI : SmoothOfRelativeDimension (n + k) W'.hom := hsm
  letI : IsClosedImmersion f.left := inferInstanceAs (IsClosedImmersion (ι.left ∣_ U))
  obtain ⟨V, hxV, ⟨b⟩⟩ := s2e_smooth_closedImmersion_conormal_frames Q' W' n k f ⟨x, hx⟩
  let a : V.toScheme ⟶ Q.left := V.ι ≫ P.ι
  letI : IsOpenImmersion a := by dsimp only [a]; infer_instance
  let eP : (Scheme.Modules.pullback P.ι).obj (s2c_conormal ι.left) ≅
      s2c_conormal (ι.left ∣_ U) :=
    (Scheme.Modules.restrictFunctorIsoPullback P.ι).symm.app (s2c_conormal ι.left) ≪≫
      s2e_conormal_restrict_ambient_open_iso ι.left U
  have ba : (Scheme.Modules.pullback a).obj (s2c_conormal ι.left) ≅
      (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Fin k) : V.toScheme.Modules) :=
    (Scheme.Modules.pullbackComp V.ι P.ι).symm.app (s2c_conormal ι.left) ≪≫
      (Scheme.Modules.pullback V.ι).mapIso eP ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm.app (s2c_conormal (ι.left ∣_ U)) ≪≫ b
  apply s2e_openImmersion_frame_neighbourhood a (s2c_conormal ι.left) k ba x
  exact ⟨⟨⟨x, hx⟩, hxV⟩, rfl⟩

end HodgeLean.Foundations.Program
