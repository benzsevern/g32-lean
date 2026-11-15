import HodgeLean.Foundations.QuotientDuality.PersistenceCutoffDeformation

/-! Actual homotopies from cutoff extensions of local deformations. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual endpoint map of the cutoff extension. -/
def persistenceCutoffEndMap
    {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (β : C(X, unitInterval)) (H : C(unitInterval × U, X))
    (hzero : ∀ u : U, H (0, u) = u.val)
    (S : Set X) (hS : IsClosed S) (hSU : S ⊆ U)
    (hβ : ∀ x, x ∉ S → β x = 0) : C(X, X) :=
  ⟨fun x => persistenceCutoffDeformation U β H (1, x),
    (persistence_cutoff_deformation_continuous U hU β H hzero S hS hSU hβ).comp
      (continuous_const.prodMk continuous_id)⟩

/-- The cutoff extension as a continuous homotopy on the entire ambient space. -/
def persistenceCutoffHomotopy
    {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (β : C(X, unitInterval)) (H : C(unitInterval × U, X))
    (hzero : ∀ u : U, H (0, u) = u.val)
    (S : Set X) (hS : IsClosed S) (hSU : S ⊆ U)
    (hβ : ∀ x, x ∉ S → β x = 0) :
    ContinuousMap.Homotopy (ContinuousMap.id X)
      (persistenceCutoffEndMap U hU β H hzero S hS hSU hβ) where
  toFun := persistenceCutoffDeformation U β H
  continuous_toFun := persistence_cutoff_deformation_continuous U hU β H hzero S hS hSU hβ
  map_zero_left := persistence_cutoff_deformation_zero_time U β H hzero
  map_one_left _ := rfl

end HodgeLean.Foundations.QuotientDuality
