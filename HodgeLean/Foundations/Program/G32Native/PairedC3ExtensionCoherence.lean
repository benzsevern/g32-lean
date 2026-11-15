import HodgeLean.Foundations.Program.G32Native.PairedC3FreeExtensionLocalFrame
import HodgeLean.Foundations.Program.G32Native.PairedC3MixedFixedFrames
import HodgeLean.Foundations.Program.G32Native.PairedConormalFreeStabilizedFrame

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Quasicoherence on pointwise open restrictions gives quasicoherence of the original module. -/
theorem paired_c3_quasicoherent_of_open_restrictions {X : Scheme.{0}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (M.restrict U.ι).IsQuasicoherent) :
    M.IsQuasicoherent := by
  choose U hx hU using h
  have hq (x : X) : SheafOfModules.IsQuasicoherent (M.over (U x)) := by
    letI := hU x
    let G := (Opens.overEquivalence (U x)).symm.inverse
    letI : G.IsDenseSubsite ((Opens.grothendieckTopology X).over (U x))
        (Opens.grothendieckTopology (U x)) :=
      (U x).instIsDenseSubsiteOverSubtypeMemOverGrothendieckTopologyFunctorOverEquivalence
    have hg : CoverPreserving ((Opens.grothendieckTopology X).over (U x))
        (Opens.grothendieckTopology (U x)) G := CoverPreserving.of_isContinuous G _ _
    have hpost : ∀ W : Over (U x), (Over.post (X := W) G).IsContinuous
        (((Opens.grothendieckTopology X).over (U x)).over W)
        ((Opens.grothendieckTopology (U x)).over (G.obj W)) :=
      fun W => Functor.isContinuous_of_coverPreserving
        (compatiblePreservingOfFlat _ _)
        (hg.overPost W)
    have h : SheafOfModules.IsQuasicoherent
        ((overEquiv (U x)).inverse.obj (M.restrict (U x).ι)) := by
      exact @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
        _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ _
        ((U x).sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)
        _ _ hpost _ _ _ _
    let e : (overEquiv (U x)).inverse.obj (M.restrict (U x).ι) ≅ M.over (U x) :=
      (overEquiv (U x)).inverse.mapIso ((overFunctorEquiv (U x)).app M).symm ≪≫
        ((overEquiv (U x)).unitIso.app (M.over (U x))).symm
    exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over (U x))).prop_of_iso e h
  letI := hq
  apply SheafOfModules.IsQuasicoherent.of_coversTop M U
  rw [Opens.coversTop_iff]
  exact top_unique fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩

/-- Restricting the original sequence to a scheme open preserves short exactness. -/
theorem paired_c3_extension_restrict_shortExact {X : Scheme.{0}}
    (T : ShortComplex X.Modules) (hT : T.ShortExact) (U : X.Opens) :
    (T.map (restrictFunctor U.ι)).ShortExact := by
  letI := paired_module_over_preservesFiniteLimits X U
  letI : PreservesFiniteLimits
      (SheafOfModules.overFunctor X.ringCatSheaf U ⋙ (overEquiv U).functor) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteLimits (restrictFunctor U.ι) :=
    preservesFiniteLimits_of_natIso (overFunctorEquiv U)
  exact hT.map_of_exact _

/-- The extension in N.4 has a quasicoherent middle term without an added input.
Source: Hartshorne, Algebraic Geometry, II.5, local splitting of bundle extensions. -/
theorem paired_c3_route_n_extension_middle_quasicoherent
    (k a b : ℕ) (T : ShortComplex (pairedC3Proj k).Modules) (hT : T.ShortExact)
    (e₁ : T.X₁ ≅ (SheafOfModules.free (Fin a) ⊞
      SheafOfModules.unit (pairedC3Proj k).ringCatSheaf))
    (e₃ : T.X₃ ≅ pairedC3SplitBundle k 0 b) : T.X₂.IsQuasicoherent := by
  apply paired_c3_quasicoherent_of_open_restrictions
  intro x
  obtain ⟨U, hx, ⟨eU⟩⟩ := paired_c3_split_bundle_fixed_frames k 0 b x
  have eU' : (Scheme.Modules.pullback U.ι).obj (pairedC3SplitBundle k 0 b) ≅
      SheafOfModules.free (Fin b) := by simpa only [Nat.zero_add] using eU
  let F := restrictFunctor U.ι
  let P := Scheme.Modules.pullback U.ι
  let S := T.map F
  have hS : S.ShortExact := paired_c3_extension_restrict_shortExact T hT U
  let e₁' : S.X₁ ≅ SheafOfModules.free (Fin (a + 1)) :=
    F.mapIso (e₁ ≪≫ (paired_free_biprod_unitFinIso (pairedC3Proj k) a).symm) ≪≫
      (restrictFunctorIsoPullback U.ι).app _ ≪≫
        SheafOfModules.pullbackObjFreeIso U.ι.toRingCatSheafHom (Fin (a + 1))
  let e₃' : S.X₃ ≅ SheafOfModules.free (Fin b) :=
    (restrictFunctorIsoPullback U.ι).app _ ≪≫ P.mapIso e₃ ≪≫ eU'
  letI := paired_c3_free_extension_locallyFree S hS (Fin (a + 1)) (Fin b) e₁' e₃'
  have hqc : S.X₂.IsQuasicoherent := inferInstance
  exact ⟨U, hx, hqc⟩

end HodgeLean.Foundations.Program.G32Native
