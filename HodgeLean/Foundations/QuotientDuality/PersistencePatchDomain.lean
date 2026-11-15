import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Constructions

/-! Actual open ambient domains inside relatively open chart domains. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_open_subspace_patch_domain
    {X : Type*} [TopologicalSpace X] (K : Set X) (W : Set K) (hW : IsOpen W)
    (x : X) (hxK : x ∈ interior K)
    (hxW : (⟨x, interior_subset hxK⟩ : K) ∈ W) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ lift : C(U, W),
      ∀ u : U, (lift u).val.val = u.val := by
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW
  let U := interior K ∩ O
  have hUL (u : U) : (⟨u.val, interior_subset u.property.1⟩ : K) ∈ W := by
    rw [← hOW]
    exact u.property.2
  let lift : C(U, W) := {
    toFun := fun u => ⟨⟨u.val, interior_subset u.property.1⟩, hUL u⟩
    continuous_toFun := (continuous_subtype_val.subtype_mk
      (fun u : U => interior_subset u.property.1)).subtype_mk hUL }
  refine ⟨U, isOpen_interior.inter hO, ⟨hxK, ?_⟩, lift, fun _ => rfl⟩
  change (⟨x, interior_subset hxK⟩ : K) ∈ Subtype.val ⁻¹' O
  rw [hOW]
  exact hxW

end HodgeLean.Foundations.QuotientDuality
