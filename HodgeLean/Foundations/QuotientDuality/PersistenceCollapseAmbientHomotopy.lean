import HodgeLean.Foundations.QuotientDuality.PersistenceCollapse
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.Basic

/-! Actual ambient homotopies on the specified collapse space. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual self-map induced on the collapse by a locus-preserving endpoint. -/
def persistenceCollapseSelfMap
    {X : Type*} [TopologicalSpace X] (A : Set X) (r : C(X, X))
    (hr : ∀ x, x ∈ A → r x ∈ A) :
    C(Quotient (persistenceCollapseSetoid A), Quotient (persistenceCollapseSetoid A)) :=
  ⟨Quotient.map r (by
    rintro x y (rfl | ⟨hx, hy⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hr x hx, hr y hy⟩),
    continuous_quot_map (by
      rintro x y (rfl | ⟨hx, hy⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨hr x hx, hr y hy⟩) r.continuous⟩

/-- Descend the actual ambient deformation without requiring its endpoint image to lie in the locus. -/
def persistenceCollapseAmbientHomotopy
    {X : Type*} [TopologicalSpace X] (A : Set X) (r : C(X, X))
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) r)
    (hpres : ∀ (t : unitInterval) x, x ∈ A → H (t, x) ∈ A) :
    ContinuousMap.Homotopy
      (ContinuousMap.id (Quotient (persistenceCollapseSetoid A)))
      (persistenceCollapseSelfMap A r (fun x hx => by
        rw [← H.apply_one x]
        exact hpres 1 x hx)) where
  toFun p := Quotient.liftOn p.2
    (fun x => Quotient.mk (persistenceCollapseSetoid A) (H (p.1, x))) (by
      rintro x y (rfl | ⟨hx, hy⟩)
      · rfl
      · exact Quotient.sound (Or.inr ⟨hpres p.1 x hx, hpres p.1 y hy⟩))
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact continuous_quotient_mk'.comp H.continuous
  map_zero_left q := by
    induction q using Quotient.inductionOn with | h x =>
      change Quotient.mk _ (H (0, x)) = Quotient.mk _ x
      rw [H.apply_zero]
      rfl
  map_one_left q := by
    induction q using Quotient.inductionOn with | h x =>
      change Quotient.mk _ (H (1, x)) = Quotient.mk _ (r x)
      rw [H.apply_one]

lemma persistence_collapse_ambient_homotopy_fixed
    {X : Type*} [TopologicalSpace X] (A : Set X) (r : C(X, X))
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) r)
    (hpres : ∀ (t : unitInterval) x, x ∈ A → H (t, x) ∈ A)
    (a : X) (ha : a ∈ A) (t : unitInterval) :
    persistenceCollapseAmbientHomotopy A r H hpres
      (t, Quotient.mk (persistenceCollapseSetoid A) a) =
        Quotient.mk (persistenceCollapseSetoid A) a := by
  change Quotient.mk (persistenceCollapseSetoid A) (H (t, a)) =
    Quotient.mk (persistenceCollapseSetoid A) a
  exact Quotient.sound (Or.inr ⟨hpres t a ha, ha⟩)

lemma persistence_collapse_ambient_homotopy_trajectory
    {X : Type*} [TopologicalSpace X] (A M N : Set X) (r : C(X, X))
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) r)
    (hpres : ∀ (t : unitInterval) x, x ∈ A → H (t, x) ∈ A)
    (htraj : ∀ (t : unitInterval) x, x ∈ M → H (t, x) ∈ N) :
    ∀ (t : unitInterval) z,
      z ∈ (Quotient.mk (persistenceCollapseSetoid A)) '' M →
      persistenceCollapseAmbientHomotopy A r H hpres (t, z) ∈
        (Quotient.mk (persistenceCollapseSetoid A)) '' N := by
  rintro t z ⟨x, hx, rfl⟩
  exact ⟨H (t, x), htraj t x hx, rfl⟩

lemma persistence_collapse_ambient_homotopy_endpoint
    {X : Type*} [TopologicalSpace X] (A M : Set X) (r : C(X, X))
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) r)
    (hpres : ∀ (t : unitInterval) x, x ∈ A → H (t, x) ∈ A)
    (hret : ∀ x ∈ M, r x ∈ A) (a : X) (ha : a ∈ A) :
    ∀ z, z ∈ (Quotient.mk (persistenceCollapseSetoid A)) '' M →
      persistenceCollapseAmbientHomotopy A r H hpres (1, z) =
        Quotient.mk (persistenceCollapseSetoid A) a := by
  rintro z ⟨x, hx, rfl⟩
  change Quotient.mk (persistenceCollapseSetoid A) (H (1, x)) =
    Quotient.mk (persistenceCollapseSetoid A) a
  rw [H.apply_one]
  exact Quotient.sound (Or.inr ⟨hret x hx, ha⟩)

end HodgeLean.Foundations.QuotientDuality
