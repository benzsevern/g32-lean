import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalFreeness

/-! # Transport of actual local frames under arbitrary scheme pullback -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Frames expressed using actual scheme pullback also give local freeness. -/
theorem paired_module_locallyFree_of_pullbackFrames {X : Scheme.{0}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ I : Type,
      Nonempty (SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
        (Scheme.Modules.pullback U.ι).obj M)) : M.IsLocallyFree := by
  apply paired_module_locallyFree_of_localFrames M
  intro x
  obtain ⟨U, hx, I, ⟨e⟩⟩ := h x
  let E := Scheme.Modules.overEquiv U
  let e' : SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅ E.functor.obj (M.over U) :=
    e ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫
      (Scheme.Modules.overFunctorEquiv U).symm.app M
  refine ⟨U, hx, I, ⟨?_⟩⟩
  let eUnit : E.functor.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf := Iso.refl _
  let η := E.unitIso.app (SheafOfModules.unit (X.ringCatSheaf.over U)) ≪≫
    E.inverse.mapIso eUnit
  exact SheafOfModules.mapFreeIso E.inverse I η ≪≫
    E.inverse.mapIso e' ≪≫ E.unitIso.symm.app (M.over U)

/-- Local freeness supplies an actual scheme pullback frame near every point. -/
theorem paired_module_local_pullbackFrame {X : Scheme.{0}} (M : X.Modules)
    [M.IsLocallyFree] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ I : Type,
      Nonempty (SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
        (Scheme.Modules.pullback U.ι).obj M) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData (M := M)
  letI := hq
  obtain ⟨W, f, hW, hxW⟩ := q.coversTop ⊤ x (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff q.X f).mp hW
  let U : X.Opens := q.X i
  let I := (q.generators i).I
  let e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U :=
    asIso (q.generators i).π
  let F := (Scheme.Modules.overEquiv U).functor
  exact ⟨U, leOfHom g hxW, I, ⟨SheafOfModules.mapFreeIso F I (Iso.refl _) ≪≫
    F.mapIso e ≪≫ (Scheme.Modules.overFunctorEquiv U).app M ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M⟩⟩

/-- Pull back the specified frame to the inverse image of its scheme open,
retaining the original index type. -/
def paired_module_framePullbackIso {X Y : Scheme.{0}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (I : Type)
    (e : SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
      (Scheme.Modules.pullback U.ι).obj M) :
    SheafOfModules.free (R := (f ⁻¹ᵁ U).toScheme.ringCatSheaf) I ≅
      (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback f).obj M) := by
  let W : X.Opens := f ⁻¹ᵁ U
  let a := f ∣_ U
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  exact (SheafOfModules.pullbackObjFreeIso a.toRingCatSheafHom I).symm ≪≫
    (Scheme.Modules.pullback a).mapIso e ≪≫
    (Scheme.Modules.pullbackComp a U.ι).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U)).app M ≪≫
    (Scheme.Modules.pullbackComp W.ι f).symm.app M

/-- Scheme pullback preserves local freeness, using the inverse images of
actual frame opens and the canonical pullback composition maps. -/
theorem paired_module_pullback_locallyFree {X Y : Scheme.{0}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsLocallyFree] : ((Scheme.Modules.pullback f).obj M).IsLocallyFree := by
  apply paired_module_locallyFree_of_pullbackFrames
  intro x
  obtain ⟨U, hx, I, ⟨e⟩⟩ := paired_module_local_pullbackFrame M (f x)
  exact ⟨f ⁻¹ᵁ U, hx, I, ⟨paired_module_framePullbackIso f M U I e⟩⟩

end HodgeLean.Foundations.Program.G32Native
