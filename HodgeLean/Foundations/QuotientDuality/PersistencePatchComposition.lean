import Mathlib.Topology.Homotopy.Basic

/-! Actual ordered composites of the finite ambient patch maps. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Apply the listed ambient patches in their specified order. -/
def persistencePatchComposite {X ι : Type*} [TopologicalSpace X]
    (R : ι → C(X, X)) : List ι → C(X, X)
  | [] => ContinuousMap.id X
  | i :: l => (persistencePatchComposite R l).comp (R i)

lemma persistence_patch_composite_fixed {X ι : Type*} [TopologicalSpace X]
    (A : Set X) (R : ι → C(X, X)) (hR : ∀ i a, a ∈ A → R i a = a)
    (l : List ι) : ∀ a, a ∈ A → persistencePatchComposite R l a = a := by
  induction l with
  | nil => intro a ha; rfl
  | cons i l ih =>
    intro a ha
    change persistencePatchComposite R l (R i a) = a
    rw [hR i a ha]
    exact ih a ha

/-- Concatenate the actual ambient patch homotopies in the specified order. -/
def persistencePatchCompositeHomotopy {X ι : Type*} [TopologicalSpace X]
    (R : ι → C(X, X))
    (G : ∀ i, ContinuousMap.Homotopy (ContinuousMap.id X) (R i)) :
    (l : List ι) → ContinuousMap.Homotopy (ContinuousMap.id X) (persistencePatchComposite R l)
  | [] => ContinuousMap.Homotopy.refl (ContinuousMap.id X)
  | i :: l => (G i).trans ((persistencePatchCompositeHomotopy R G l).compContinuousMap (R i))

lemma persistence_patch_composite_homotopy_fixed {X ι : Type*} [TopologicalSpace X]
    (A : Set X) (R : ι → C(X, X))
    (G : ∀ i, ContinuousMap.Homotopy (ContinuousMap.id X) (R i))
    (hG : ∀ i (t : unitInterval) a, a ∈ A → G i (t, a) = a)
    (l : List ι) : ∀ (t : unitInterval) a, a ∈ A →
      persistencePatchCompositeHomotopy R G l (t, a) = a := by
  induction l with
  | nil => intro t a ha; rfl
  | cons i l ih =>
    intro t a ha
    change ((G i).trans ((persistencePatchCompositeHomotopy R G l).compContinuousMap (R i)))
      (t, a) = a
    rw [(G i).trans_apply
      ((persistencePatchCompositeHomotopy R G l).compContinuousMap (R i)) (t, a)]
    split_ifs
    · exact hG i _ a ha
    · have hR : R i a = a := by
        have h := hG i 1 a ha
        rw [(G i).apply_one] at h
        exact h
      change persistencePatchCompositeHomotopy R G l (_, R i a) = a
      rw [hR]
      exact ih _ a ha

end HodgeLean.Foundations.QuotientDuality
