import HodgeLean.Foundations.Program.G32Native.PairedC3LocalUnitLift
import HodgeLean.Foundations.Program.G32Native.PairedC3LocalFreeDescent
import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalFrameIso
import HodgeLean.Foundations.Program.G32Native.UnionConormalRestrictionExact

/-! # Local frames of extensions with free endpoints -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Free endpoints, with a finite free quotient, force the arbitrary middle
sheaf of a short exact sequence to be locally free.
Source: Hartshorne, Algebraic Geometry, II.5, locally free sheaves and local splitting. -/
theorem paired_c3_free_endpoints_locallyFree {X : Scheme.{0}}
    (E : ShortComplex X.Modules) (hE : E.ShortExact)
    (I J : Type) [Finite J]
    (e₁ : E.X₁ ≅ SheafOfModules.free I)
    (e₃ : E.X₃ ≅ SheafOfModules.free J) : E.X₂.IsLocallyFree := by
  letI := hE.epi_g
  apply paired_module_locallyFree_of_pullbackFrames
  intro x
  obtain ⟨U, hx, s, hs⟩ := paired_c3_free_quotient_local_section E.g J e₃ x
  let F := Scheme.Modules.restrictFunctor U.ι
  let T := E.map F
  have hT : T.ShortExact := unionConormal_restrict_shortExact U.ι E hE
  let eF₁ : T.X₁ ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I :=
    F.mapIso e₁ ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
      SheafOfModules.pullbackObjFreeIso U.ι.toRingCatSheafHom I
  let eF₃ : T.X₃ ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) J :=
    F.mapIso e₃ ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
      SheafOfModules.pullbackObjFreeIso U.ι.toRingCatSheafHom J
  let split := ShortComplex.Splitting.ofExactOfSection T hT.exact s hs hT.mono_f
  let frame : T.X₂ ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) (I ⊕ J) :=
    split.isoBinaryBiproduct ≪≫ biprod.mapIso eF₁ eF₃ ≪≫
      biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso I J
  exact ⟨U, hx, I ⊕ J, ⟨frame.symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app E.X₂⟩⟩

#print axioms paired_c3_free_endpoints_locallyFree
/-- Local free endpoint frames with finite quotient rank force local
freeness of the original middle sheaf, without a quasicoherence premise.
Source: Hartshorne, Algebraic Geometry, II.5, locally free sheaves and local splitting. -/
theorem paired_c3_extension_locallyFree_of_frames {X : Scheme.{0}}
    (E : ShortComplex X.Modules) (hE : E.ShortExact)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ I J : Type,
      Finite J ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj E.X₁ ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj E.X₃ ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) J)) :
    E.X₂.IsLocallyFree := by
  apply paired_c3_locallyFree_of_local_pullbacks
  intro x
  obtain ⟨U, hx, I, J, hJ, ⟨e₁⟩, ⟨e₃⟩⟩ := h x
  letI := hJ
  let T := E.map (Scheme.Modules.restrictFunctor U.ι)
  have hT : T.ShortExact := unionConormal_restrict_shortExact U.ι E hE
  let eT₁ : T.X₁ ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app E.X₁ ≪≫ e₁
  let eT₃ : T.X₃ ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) J :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app E.X₃ ≪≫ e₃
  letI : T.X₂.IsLocallyFree := paired_c3_free_endpoints_locallyFree T hT I J eT₁ eT₃
  letI : ((Scheme.Modules.restrictFunctor U.ι).obj E.X₂).IsLocallyFree :=
    inferInstanceAs T.X₂.IsLocallyFree
  exact ⟨U, hx, paired_module_locallyFree_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app E.X₂)⟩

#print axioms paired_c3_extension_locallyFree_of_frames
end HodgeLean.Foundations.Program.G32Native
