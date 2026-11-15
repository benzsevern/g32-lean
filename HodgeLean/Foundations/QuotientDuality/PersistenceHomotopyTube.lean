import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Maps.Proper.Basic

/-! Open trajectory neighbourhoods for homotopies fixing the locus. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_fixed_homotopy_neighbourhood_shrink
    {X : Type*} [TopologicalSpace X] (A : Set X) (r : C(X, X))
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) r)
    (hfixed : ∀ (t : unitInterval) a, a ∈ A → H (t, a) = a)
    (U : Set X) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ V : Set X, IsOpen V ∧ A ⊆ V ∧ V ⊆ U ∧
      ∀ (t : unitInterval) x, x ∈ V → H (t, x) ∈ U := by
  let V : Set X := (Prod.snd '' (H ⁻¹' Uᶜ))ᶜ
  have hV : IsOpen V :=
    (isClosedMap_snd_of_compactSpace _ (hU.isClosed_compl.preimage H.continuous)).isOpen_compl
  have hAV : A ⊆ V := by
    intro a ha
    rintro ⟨⟨t, y⟩, hy, hya⟩
    change y = a at hya
    subst y
    exact hy (by rw [hfixed t a ha]; exact hAU ha)
  have htraj : ∀ (t : unitInterval) x, x ∈ V → H (t, x) ∈ U := by
    intro t x hx
    by_contra h
    exact hx ⟨(t, x), h, rfl⟩
  refine ⟨V, hV, hAV, ?_, htraj⟩
  intro x hx
  have h := htraj 0 x hx
  rw [H.apply_zero] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
