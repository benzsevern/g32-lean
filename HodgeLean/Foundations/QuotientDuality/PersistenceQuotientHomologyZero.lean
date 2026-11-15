import HodgeLean.Foundations.QuotientDuality.PersistenceCollapseAmbientHomotopy
import HodgeLean.Foundations.QuotientDuality.PersistenceNeighbourhoodHomologyZero

/-! Zero relative homology maps on the actual quotient neighbourhood images. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_quotient_neighbourhood_inclusion_relative_homology_zero
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A M N : Set X) (hMN : M ⊆ N) (r : C(X, X))
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) r)
    (hfixed : ∀ (t : unitInterval) a, a ∈ A → H (t, a) = a)
    (htraj : ∀ (t : unitInterval) x, x ∈ M → H (t, x) ∈ N)
    (hret : ∀ x ∈ M, r x ∈ A) (a : X) (ha : a ∈ A) (n : ℕ) :
    relativeHomologyMap K n (persistenceNeighbourhoodPairInclusion
      ({Quotient.mk (persistenceCollapseSetoid A) a})
      ((Quotient.mk (persistenceCollapseSetoid A)) '' M)
      ((Quotient.mk (persistenceCollapseSetoid A)) '' N) (Set.image_mono hMN)) = 0 := by
  have hpres : ∀ (t : unitInterval) x, x ∈ A → H (t, x) ∈ A := by
    intro t x hx
    rw [hfixed t x hx]
    exact hx
  let rQ := persistenceCollapseSelfMap A r (fun x hx => by
    rw [← H.apply_one x]
    exact hpres 1 x hx)
  let HQ := persistenceCollapseAmbientHomotopy A r H hpres
  apply persistence_neighbourhood_pair_inclusion_relative_homology_zero K _ _ _
    (Set.image_mono hMN) rQ HQ _ _ _ n
  · intro t z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact persistence_collapse_ambient_homotopy_fixed A r H hpres a ha t
  · exact persistence_collapse_ambient_homotopy_trajectory A M N r H hpres htraj
  · intro z hz
    apply Set.mem_singleton_iff.mpr
    have h := persistence_collapse_ambient_homotopy_endpoint A M r H hpres hret a ha z hz
    change HQ (1, z) = _ at h
    rw [HQ.apply_one] at h
    exact h

end HodgeLean.Foundations.QuotientDuality
