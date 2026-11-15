import HodgeLean.Foundations.QuotientDuality.PersistenceLocalPatch
import HodgeLean.Foundations.QuotientDuality.PersistencePatchDomain

/-! Actual global patches obtained from local subspace deformations. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_subspace_deformation_global_patch
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (K A : Set X) (W : Set K) (hW : IsOpen W)
    (H : C(unitInterval × W, X)) (hzero : ∀ w : W, H (0, w) = w.val.val)
    (hfixed : ∀ (t : unitInterval) (w : W), w.val.val ∈ A → H (t, w) = w.val.val)
    (hret : ∀ w : W, H (1, w) ∈ A)
    (x : X) (hxK : x ∈ interior K) (hxW : (⟨x, interior_subset hxK⟩ : K) ∈ W) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ (R : C(X, X))
      (G : ContinuousMap.Homotopy (ContinuousMap.id X) R),
      (∀ (t : unitInterval) (a : X), a ∈ A → G (t, a) = a) ∧
      ∀ y ∈ V, R y ∈ A := by
  obtain ⟨U, hU, hxU, lift, hlift⟩ :=
    persistence_open_subspace_patch_domain K W hW x hxK hxW
  let Hopen : C(unitInterval × U, X) := H.comp
    ⟨fun p => (p.1, lift p.2), continuous_fst.prodMk (lift.continuous.comp continuous_snd)⟩
  apply persistence_local_deformation_global_patch U A hU Hopen _ _ _ x hxU
  · intro u
    exact (hzero (lift u)).trans (hlift u)
  · intro t u hu
    have ha : (lift u).val.val ∈ A := by rw [hlift]; exact hu
    exact (hfixed t (lift u) ha).trans (hlift u)
  · intro u
    exact hret (lift u)

end HodgeLean.Foundations.QuotientDuality
