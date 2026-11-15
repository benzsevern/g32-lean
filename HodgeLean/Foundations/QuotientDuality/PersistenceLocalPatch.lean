import HodgeLean.Foundations.QuotientDuality.PersistenceCutoffHomotopy
import HodgeLean.Foundations.QuotientDuality.PersistenceCutoffExistence

/-! Actual global homotopy patches supplied by local fixed deformations. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_local_deformation_global_patch
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (U A : Set X) (hU : IsOpen U) (H : C(unitInterval × U, X))
    (hzero : ∀ u : U, H (0, u) = u.val)
    (hfixed : ∀ (t : unitInterval) (u : U), u.val ∈ A → H (t, u) = u.val)
    (hret : ∀ u : U, H (1, u) ∈ A) (x : X) (hx : x ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ (R : C(X, X))
      (G : ContinuousMap.Homotopy (ContinuousMap.id X) R),
      (∀ (t : unitInterval) (a : X), a ∈ A → G (t, a) = a) ∧
      ∀ y ∈ V, R y ∈ A := by
  obtain ⟨V, S, β, hV, hxV, hS, hSU, hβ, hone⟩ :=
    persistence_neighbourhood_cutoff U hU x hx
  let R := persistenceCutoffEndMap U hU β H hzero S hS hSU hβ
  let G := persistenceCutoffHomotopy U hU β H hzero S hS hSU hβ
  refine ⟨V, hV, hxV, R, G, ?_, ?_⟩
  · intro t a ha
    exact persistence_cutoff_deformation_fixed U A β H hfixed t a ha
  · intro y hy
    have hyS : y ∈ S := by
      by_contra hyS
      have h01 : (0 : unitInterval) = 1 := (hβ y hyS).symm.trans (hone y hy)
      exact zero_ne_one h01
    change persistenceCutoffDeformation U β H (1, y) ∈ A
    rw [persistence_cutoff_deformation_full_time U β H y (hSU hyS) (hone y hy)]
    exact hret ⟨y, hSU hyS⟩

end HodgeLean.Foundations.QuotientDuality
