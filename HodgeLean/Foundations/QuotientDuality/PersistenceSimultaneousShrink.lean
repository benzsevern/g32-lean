import HodgeLean.Foundations.QuotientDuality.PersistenceQuotientHomologyZero
import HodgeLean.Foundations.QuotientDuality.PersistenceCollapseComplement

/-! One actual neighbourhood shrink for both original and collapsed pair maps. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_simultaneous_relative_homology_shrink
    (K : Type) [CommRing K] {X : Type} [TopologicalSpace X]
    (A N : Set X) (hN : IsOpen N) (hAN : A ⊆ N) (r : C(X, X))
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) r)
    (hfixed : ∀ (t : unitInterval) a, a ∈ A → H (t, a) = a)
    (hret : ∀ x ∈ N, r x ∈ A) (U : Set X) (hU : IsOpen U) (hAU : A ⊆ U)
    (a : X) (ha : a ∈ A) :
    ∃ M : Set X, IsOpen M ∧ A ⊆ M ∧
      IsOpen ((Quotient.mk (persistenceCollapseSetoid A)) '' M) ∧
      ∃ hMU : M ⊆ U, ∀ n : ℕ,
        relativeHomologyMap K n (persistenceNeighbourhoodPairInclusion A M U hMU) = 0 ∧
        relativeHomologyMap K n (persistenceNeighbourhoodPairInclusion
          ({Quotient.mk (persistenceCollapseSetoid A) a})
          ((Quotient.mk (persistenceCollapseSetoid A)) '' M)
          ((Quotient.mk (persistenceCollapseSetoid A)) '' U) (Set.image_mono hMU)) = 0 := by
  obtain ⟨M₀, hM₀, hAM₀, hM₀U, htraj⟩ :=
    persistence_fixed_homotopy_neighbourhood_shrink A r H hfixed U hU hAU
  let M := M₀ ∩ N
  have hM : IsOpen M := hM₀.inter hN
  have hAM : A ⊆ M := fun x hx => ⟨hAM₀ hx, hAN hx⟩
  have hMU : M ⊆ U := fun x hx => hM₀U hx.1
  refine ⟨M, hM, hAM, persistence_collapse_neighbourhood_isOpen A M hAM hM, hMU, ?_⟩
  intro n
  refine ⟨persistence_neighbourhood_pair_inclusion_relative_homology_zero K A M U hMU r H
    hfixed (fun t x hx => htraj t x hx.1) (fun x hx => hret x hx.2) n, ?_⟩
  exact persistence_quotient_neighbourhood_inclusion_relative_homology_zero K A M U hMU r H
    hfixed (fun t x hx => htraj t x hx.1) (fun x hx => hret x hx.2) a ha n

end HodgeLean.Foundations.QuotientDuality
