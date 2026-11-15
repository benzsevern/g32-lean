import HodgeLean.Foundations.QuotientDuality.PersistenceCollapse
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.Contractible

/-! Descending neighbourhood deformations to collapse spaces. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- The contraction induced by a deformation into the collapsed locus. -/
def persistenceCollapseContraction
    {X : Type*} [TopologicalSpace X] (A : Set X)
    (r : C(X, X)) (H : ContinuousMap.Homotopy (ContinuousMap.id X) r)
    (hpres : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ A)
    (hr : ∀ x, r x ∈ A) (a : X) (ha : a ∈ A) :
    ContinuousMap.Homotopy
      (ContinuousMap.id (Quotient (persistenceCollapseSetoid A)))
      (ContinuousMap.const _ (Quotient.mk (persistenceCollapseSetoid A) a)) where
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
      change Quotient.mk _ (H (1, x)) = Quotient.mk _ a
      rw [H.apply_one]
      exact Quotient.sound (Or.inr ⟨hr x, ha⟩)

lemma persistence_collapse_contractible_of_deformation
    {X : Type*} [TopologicalSpace X] (A : Set X)
    (r : C(X, X)) (H : ContinuousMap.Homotopy (ContinuousMap.id X) r)
    (hpres : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ A)
    (hr : ∀ x, r x ∈ A) (hA : A.Nonempty) :
    ContractibleSpace (Quotient (persistenceCollapseSetoid A)) := by
  obtain ⟨a, ha⟩ := hA
  apply (contractible_iff_id_nullhomotopic _).mpr
  exact ⟨Quotient.mk _ a, ⟨persistenceCollapseContraction A r H hpres hr a ha⟩⟩

end HodgeLean.Foundations.QuotientDuality
