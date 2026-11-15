import HodgeLean.Foundations.Program.G32Native.PairedC3DualInvertible
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects
import HodgeLean.Foundations.Program.G32Native.PairedConormalQuasicoherent
import HodgeLean.Foundations.Program.G32Native.PairedC3SplitBundleVanishing

/-! # Local freeness and section lifting for Route N mixed bundles -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Binary sums retain actual local free frames. -/
theorem paired_c3_biprod_locallyFree {X : Scheme.{0}} (M N : X.Modules)
    [M.IsLocallyFree] [N.IsLocallyFree] : (M ⊞ N).IsLocallyFree := by
  apply paired_module_locallyFree_of_pullbackFrames
  intro x
  obtain ⟨U, hxU, I, ⟨eM⟩⟩ := paired_module_local_pullbackFrame M x
  obtain ⟨V, hxV, J, ⟨eN⟩⟩ := paired_module_local_pullbackFrame N x
  let W := U ⊓ V
  let F := Scheme.Modules.pullback W.ι
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let eM' := paired_module_frame_refineIso M (show W ≤ U from inf_le_left) I eM
  let eN' := paired_module_frame_refineIso N (show W ≤ V from inf_le_right) J eN
  refine ⟨W, ⟨hxU, hxV⟩, I ⊕ J, ⟨?_⟩⟩
  exact (SheafOfModules.freeSumIso (R := W.toScheme.ringCatSheaf) I J).symm ≪≫
    (biprod.isoCoprod _ _).symm ≪≫ biprod.mapIso eM' eN' ≪≫
    (F.mapBiprod M N).symm

/-- A unit frame of an invertible sheaf gives an actual local free frame. -/
theorem paired_c3_invertible_locallyFree {X : Scheme.{0}} (M : X.Modules)
    (hM : IsInvertible M) : M.IsLocallyFree := by
  apply paired_module_locallyFree_of_pullbackFrames
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hM.exists_trivialization x
  exact ⟨U, hx, PUnit, ⟨coproductUniqueIso
    (fun _ : PUnit => SheafOfModules.unit U.toScheme.ringCatSheaf) ≪≫ e.symm⟩⟩

/-- The actual negative line and recursive sums are locally free. -/
theorem paired_c3_split_bundle_locallyFree (k a b : ℕ) :
    (pairedC3SplitBundle k a b).IsLocallyFree := by
  haveI : (pairedC3NegativeLine k).IsLocallyFree :=
    paired_c3_invertible_locallyFree _
      (paired_c3_dual_invertible (ProjSpace.isInvertible_twistingSheaf ℂ k))
  induction b with
  | zero => exact inferInstanceAs (SheafOfModules.free (Fin a)).IsLocallyFree
  | succ b ih =>
    letI := ih
    exact paired_c3_biprod_locallyFree _ _

/-- Quasicoherence of the original mixed kernel needs no additional input. -/
theorem paired_c3_split_bundle_quasicoherent (k a b : ℕ) :
    (pairedC3SplitBundle k a b).IsQuasicoherent := by
  letI := paired_c3_split_bundle_locallyFree k a b
  infer_instance

/-- The actual quotient sections lift using only middle-object quasicoherence. -/
theorem paired_c3_mixed_kernel_global_lift (k a b : ℕ) (hk : 0 < k)
    (E : ShortComplex (pairedC3Proj k).Modules) (hE : E.ShortExact)
    [E.X₂.IsQuasicoherent] (e : E.X₁ ≅ pairedC3SplitBundle k a b) :
    Function.Surjective (E.g.app ⊤) := by
  letI : E.X₁.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (pairedC3Proj k).ringCatSheaf).prop_of_iso
      ((sheafOfModulesEquivalence _).functor.mapIso e.symm)
      (paired_c3_split_bundle_quasicoherent k a b)
  letI := conormal_shortExact_last_quasicoherent E hE
  exact paired_c3_split_kernel_global_lift k hk a b E hE e

#print axioms paired_c3_biprod_locallyFree
#print axioms paired_c3_invertible_locallyFree
#print axioms paired_c3_split_bundle_locallyFree
#print axioms paired_c3_split_bundle_quasicoherent
#print axioms paired_c3_mixed_kernel_global_lift
end HodgeLean.Foundations.Program.G32Native
