import HodgeLean.Foundations.Program.G32Native.PairedC3MixedBundleCoherence

/-! # Fixed-rank frames of the original Route N mixed bundles -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Fixed-rank frames of two actual modules give frames of their binary
sum, of the sum rank, on the intersection of the supplied frame opens. -/
theorem paired_c3_biprod_fixed_frames {X : Scheme.{0}} (M N : X.Modules)
    (m n : ℕ)
    (hM : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty
      ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.free (Fin m)))
    (hN : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty
      ((Scheme.Modules.pullback U.ι).obj N ≅ SheafOfModules.free (Fin n)))
    (x : X) : ∃ U : X.Opens, x ∈ U ∧ Nonempty
      ((Scheme.Modules.pullback U.ι).obj (M ⊞ N) ≅
        SheafOfModules.free (Fin (m + n))) := by
  obtain ⟨U, hxU, ⟨eM⟩⟩ := hM x
  obtain ⟨V, hxV, ⟨eN⟩⟩ := hN x
  let W := U ⊓ V
  let F := Scheme.Modules.pullback W.ι
  letI : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let eM' := paired_module_frame_refineIso M (show W ≤ U from inf_le_left) (Fin m) eM.symm
  let eN' := paired_module_frame_refineIso N (show W ≤ V from inf_le_right) (Fin n) eN.symm
  refine ⟨W, ⟨hxU, hxV⟩, ⟨?_⟩⟩
  exact F.mapBiprod M N ≪≫ biprod.mapIso eM'.symm eN'.symm ≪≫
    biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso (Fin m) (Fin n) ≪≫
      (SheafOfModules.freeFunctor (R := W.toScheme.ringCatSheaf)).mapIso finSumFinEquiv.toIso

/-- Every original mixed bundle has local frames of its specified rank. -/
theorem paired_c3_split_bundle_fixed_frames (k a b : ℕ) :
    ∀ x : pairedC3Proj k, ∃ U : (pairedC3Proj k).Opens, x ∈ U ∧ Nonempty
      ((Scheme.Modules.pullback U.ι).obj (pairedC3SplitBundle k a b) ≅
        SheafOfModules.free (Fin (a + b))) := by
  have hn : ∀ x : pairedC3Proj k, ∃ U : (pairedC3Proj k).Opens, x ∈ U ∧ Nonempty
      ((Scheme.Modules.pullback U.ι).obj (pairedC3NegativeLine k) ≅
        SheafOfModules.free (Fin 1)) := by
    intro x
    obtain ⟨U, hx, ⟨e⟩⟩ := (paired_c3_dual_invertible
      (ProjSpace.isInvertible_twistingSheaf ℂ k)).exists_trivialization x
    exact ⟨U, hx, ⟨e ≪≫ (coproductUniqueIso
      (fun _ : Fin 1 => SheafOfModules.unit U.toScheme.ringCatSheaf)).symm⟩⟩
  induction b with
  | zero =>
    intro x
    exact ⟨⊤, trivial, ⟨SheafOfModules.pullbackObjFreeIso
      (⊤ : (pairedC3Proj k).Opens).ι.toRingCatSheafHom (Fin a)⟩⟩
  | succ b ih =>
    exact paired_c3_biprod_fixed_frames (pairedC3SplitBundle k a b)
      (pairedC3NegativeLine k) (a + b) 1 ih hn

#print axioms paired_c3_split_bundle_fixed_frames
#print axioms paired_c3_biprod_fixed_frames
end HodgeLean.Foundations.Program.G32Native
