import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalFrameIso

/-! # Local freeness from open restrictions that are themselves locally free -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Locally free pullbacks on neighborhoods give local freeness of the
original module, retaining the original open immersion into the scheme. -/
theorem paired_c3_locallyFree_of_local_pullbacks {X : Scheme.{0}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ((Scheme.Modules.pullback U.ι).obj M).IsLocallyFree) : M.IsLocallyFree := by
  apply paired_module_locallyFree_of_pullbackFrames
  intro x
  obtain ⟨U, hx, hM⟩ := h x
  letI := hM
  let y : U.toScheme := ⟨x, hx⟩
  obtain ⟨V, hy, I, ⟨b⟩⟩ := paired_module_local_pullbackFrame
    ((Scheme.Modules.pullback U.ι).obj M) y
  let f := V.ι ≫ U.ι
  let W := f.opensRange
  let e : V.toScheme ≅ W.toScheme := f.isoOpensRange
  have he : e.inv ≫ f = W.ι := by
    rw [← Scheme.Hom.isoOpensRange_hom_ι f, Iso.inv_hom_id_assoc]
  have hxW : x ∈ W := by
    exact ⟨(⟨y, hy⟩ : V.toScheme), rfl⟩
  let c : SheafOfModules.free (R := V.toScheme.ringCatSheaf) I ≅
      (Scheme.Modules.pullback f).obj M :=
    b ≪≫ (Scheme.Modules.pullbackComp V.ι U.ι).app M
  letI : (SheafOfModules.pushforward e.inv.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward e.inv).IsRightAdjoint)
  refine ⟨W, hxW, I, ⟨?_⟩⟩
  exact (SheafOfModules.pullbackObjFreeIso e.inv.toRingCatSheafHom I).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso c ≪≫
    (Scheme.Modules.pullbackComp e.inv f).app M ≪≫
    (Scheme.Modules.pullbackCongr he).app M

#print axioms paired_c3_locallyFree_of_local_pullbacks
end HodgeLean.Foundations.Program.G32Native
