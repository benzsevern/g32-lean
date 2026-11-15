import HodgeLean.Foundations.Program.G32Native.PairedC3FreeArrowLocalLift
import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalExtension
import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalFreeness

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Extensions with free endpoints have local free frames even without
quasicoherence of the middle term as an input.
Source: Hartshorne, Algebraic Geometry, II.5, locally free sheaves. -/
theorem paired_c3_free_extension_local_frame {X : Scheme.{0}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (I J : Type) [Finite J]
    (e₁ : S.X₁ ≅ SheafOfModules.free I)
    (e₃ : S.X₃ ≅ SheafOfModules.free J) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ Nonempty
      (SheafOfModules.free (R := X.ringCatSheaf.over V) (I ⊕ J) ≅ S.X₂.over V) := by
  letI := hS.epi_g
  obtain ⟨V, hxV, l, hl⟩ := paired_c3_free_arrow_local_lift S.g e₃.inv x
  let F := SheafOfModules.overFunctor X.ringCatSheaf V
  letI : F.IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) V).isLeftAdjoint
  letI := paired_module_over_preservesFiniteLimits X V
  letI := paired_module_over_preservesFiniteColimits X V
  let T := S.map F
  have hT : T.ShortExact := hS.map_of_exact F
  let eJ : SheafOfModules.free (R := X.ringCatSheaf.over V) J ≅ F.obj S.X₃ :=
    SheafOfModules.mapFreeIso F J (Iso.refl _) ≪≫ F.mapIso e₃.symm
  have hl' : l ≫ T.g = eJ.hom := hl
  let s : T.X₃ ⟶ T.X₂ := eJ.inv ≫ l
  have hs : s ≫ T.g = 𝟙 _ := by
    rw [Category.assoc, hl', eJ.inv_hom_id]
    rfl
  let eI : T.X₁ ≅ SheafOfModules.free (R := X.ringCatSheaf.over V) I :=
    F.mapIso e₁ ≪≫ (SheafOfModules.mapFreeIso F I (Iso.refl _)).symm
  refine ⟨V, hxV, ⟨?_⟩⟩
  exact (SheafOfModules.freeSumIso I J).symm ≪≫
    (biprod.isoCoprod _ _).symm ≪≫ biprod.mapIso eI.symm eJ ≪≫
      (ShortComplex.Splitting.ofExactOfSection T hT.exact s hs hT.mono_f).isoBinaryBiproduct.symm

/-- The middle object of a finite-free endpoint extension is locally free. -/
theorem paired_c3_free_extension_locallyFree {X : Scheme.{0}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (I J : Type) [Finite J]
    (e₁ : S.X₁ ≅ SheafOfModules.free I)
    (e₃ : S.X₃ ≅ SheafOfModules.free J) : S.X₂.IsLocallyFree := by
  apply paired_module_locallyFree_of_localFrames
  intro x
  obtain ⟨V, hxV, he⟩ := paired_c3_free_extension_local_frame S hS I J e₁ e₃ x
  exact ⟨V, hxV, I ⊕ J, he⟩

end HodgeLean.Foundations.Program.G32Native
