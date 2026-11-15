import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalSection
import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalFrameIso
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Local freeness of an actual extension by a structure module -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Actual restriction to a scheme-open slice preserves finite limits. -/
theorem paired_module_over_preservesFiniteLimits (X : Scheme.{0}) (U : X.Opens) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{0} X.ringCatSheaf U) := by
  change PreservesFiniteLimits
    (SheafOfModules.pushforward.{0} (F := Over.forget U) (𝟙 (X.ringCatSheaf.over U)))
  letI : (SheafOfModules.pushforward.{0} (F := Over.forget U)
      (𝟙 (X.ringCatSheaf.over U))).IsRightAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction.{0} (F := Over.forget U)
      (𝟙 (X.ringCatSheaf.over U))).isRightAdjoint
  infer_instance

/-- Actual restriction to a scheme-open slice also preserves finite colimits. -/
theorem paired_module_over_preservesFiniteColimits (X : Scheme.{0}) (U : X.Opens) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{0} X.ringCatSheaf U) := by
  change PreservesFiniteColimits
    (SheafOfModules.pushforward.{0} (F := Over.forget U) (𝟙 (X.ringCatSheaf.over U)))
  letI : (SheafOfModules.pushforward.{0} (F := Over.forget U)
      (𝟙 (X.ringCatSheaf.over U))).IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).isLeftAdjoint
  infer_instance

/-- An actual extension of the structure module by a free sheaf has an
actual free frame near every point, with the sum index retained. -/
theorem paired_free_extension_localFrame {X : Scheme.{0}} (J : Type)
    (P : X.Modules) (f : (SheafOfModules.free (R := X.ringCatSheaf) J) ⟶ P)
    (g : P ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).ShortExact) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty
      (SheafOfModules.free (R := X.ringCatSheaf.over U) (J ⊕ PUnit) ≅ P.over U) := by
  letI : Epi g := hS.epi_g
  obtain ⟨U, hx, s, hs⟩ := paired_unit_quotient_localSplit g x
  let F := SheafOfModules.overFunctor.{0} X.ringCatSheaf U
  letI : F.IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).isLeftAdjoint
  letI : PreservesFiniteLimits F := paired_module_over_preservesFiniteLimits X U
  letI : PreservesFiniteColimits F := paired_module_over_preservesFiniteColimits X U
  letI : F.PreservesZeroMorphisms := ⟨by intros; rfl⟩
  have hmap := hS.map_of_exact F
  let split := ShortComplex.Splitting.ofExactOfSection
    ((ShortComplex.mk f g hfg).map F) hmap.exact s hs hmap.mono_f
  let ef : SheafOfModules.free (R := X.ringCatSheaf.over U) J ≅
      F.obj (SheafOfModules.free (R := X.ringCatSheaf) J) :=
    SheafOfModules.mapFreeIso F J (Iso.refl _)
  let eu : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) :=
    coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit (X.ringCatSheaf.over U))
  let e : P.over U ≅ SheafOfModules.free (R := X.ringCatSheaf.over U) (J ⊕ PUnit) :=
    split.isoBinaryBiproduct ≪≫ biprod.mapIso ef.symm eu.symm ≪≫
      biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso J PUnit
  exact ⟨U, hx, ⟨e.symm⟩⟩

/-- Local freeness of the actual extension follows from the original
short exact sequence, with no quasicoherence input. -/
theorem paired_free_extension_locallyFree {X : Scheme.{0}} (J : Type)
    (P : X.Modules) (f : (SheafOfModules.free (R := X.ringCatSheaf) J) ⟶ P)
    (g : P ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).ShortExact) :
    P.IsLocallyFree := by
  apply paired_module_locallyFree_of_localFrames P
  intro x
  obtain ⟨U, hx, e⟩ := paired_free_extension_localFrame J P f g hfg hS x
  exact ⟨U, hx, J ⊕ PUnit, e⟩

end HodgeLean.Foundations.Program.G32Native
