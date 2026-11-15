import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalFrameTransport

/-! # Actual local frames through the supplied model isomorphisms -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A specified sheaf isomorphism transports local freeness. -/
theorem paired_module_locallyFree_of_iso {X : Scheme.{0}} {M N : X.Modules}
    (e : M ≅ N) [M.IsLocallyFree] : N.IsLocallyFree := by
  apply paired_module_locallyFree_of_pullbackFrames
  intro x
  obtain ⟨U, hx, I, ⟨b⟩⟩ := paired_module_local_pullbackFrame M x
  exact ⟨U, hx, I, ⟨b ≪≫ (Scheme.Modules.pullback U.ι).mapIso e⟩⟩

/-- Pullback along a scheme isomorphism reflects local freeness. -/
theorem paired_module_locallyFree_of_isoPullback {X Y : Scheme.{0}} (e : X ≅ Y)
    (M : Y.Modules) [((Scheme.Modules.pullback e.hom).obj M).IsLocallyFree] :
    M.IsLocallyFree := by
  let P := (Scheme.Modules.pullback e.hom).obj M
  letI := paired_module_pullback_locallyFree e.inv P
  let b : (Scheme.Modules.pullback e.inv).obj P ≅ M :=
    (Scheme.Modules.pullbackComp e.inv e.hom).app M ≪≫
    (Scheme.Modules.pullbackCongr e.inv_hom_id).app M ≪≫
    (Scheme.Modules.pullbackId Y).app M
  exact paired_module_locallyFree_of_iso b

/-- Restrict a specified pullback frame to a smaller scheme open. -/
def paired_module_frame_refineIso {X : Scheme.{0}} (M : X.Modules)
    {V U : X.Opens} (h : V ≤ U) (I : Type)
    (e : SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
      (Scheme.Modules.pullback U.ι).obj M) :
    SheafOfModules.free (R := V.toScheme.ringCatSheaf) I ≅
      (Scheme.Modules.pullback V.ι).obj M := by
  let f := X.homOfLE h
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward f).IsRightAdjoint)
  exact (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).symm ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫
    (Scheme.Modules.pullbackComp f U.ι).app M ≪≫
    (Scheme.Modules.pullbackCongr (X.homOfLE_ι h)).app M

/-- A specified model identification through a scheme isomorphism transports
frames without changing their index type. -/
theorem paired_module_fixedFrames_of_isoPullback {X Y : Scheme.{0}} (e : X ≅ Y)
    (N : X.Modules) (M : Y.Modules) (E : N ≅ (Scheme.Modules.pullback e.hom).obj M)
    (I : Type)
    (hN : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
        (Scheme.Modules.pullback U.ι).obj N)) :
    ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧
      Nonempty (SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
        (Scheme.Modules.pullback U.ι).obj M) := by
  let b : (Scheme.Modules.pullback e.inv).obj N ≅ M :=
    (Scheme.Modules.pullback e.inv).mapIso E ≪≫
    (Scheme.Modules.pullbackComp e.inv e.hom).app M ≪≫
    (Scheme.Modules.pullbackCongr e.inv_hom_id).app M ≪≫
    (Scheme.Modules.pullbackId Y).app M
  intro y
  obtain ⟨U, hy, ⟨c⟩⟩ := hN (e.inv y)
  let W : Y.Opens := e.inv ⁻¹ᵁ U
  exact ⟨W, hy, ⟨paired_module_framePullbackIso e.inv N U I c ≪≫
    (Scheme.Modules.pullback W.ι).mapIso b⟩⟩

end HodgeLean.Foundations.Program.G32Native
