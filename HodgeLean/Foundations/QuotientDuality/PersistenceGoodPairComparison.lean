import HodgeLean.Foundations.QuotientDuality.PersistenceGoodPairCollapse
import HodgeLean.Foundations.QuotientDuality.PersistencePointPairs

/-! Comparison of original pairs through their actual good-pair quotient maps. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_good_pair_quotient_square
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set Y) (x : X) (hx : f x ∈ A) :
    persistencePairMap (TopCat.ofHom f) A ≫ persistenceCollapseLocusPairMap A (f x) hx =
      persistenceCollapseLocusPairMap (f ⁻¹' A) x hx ≫
        persistencePointPairMap (TopCat.ofHom (persistenceCollapseContinuousMap f f.continuous A))
          (Quotient.mk (persistenceCollapseSetoid (f ⁻¹' A)) x) := by
  apply persistence_pair_hom_ext
  rfl

lemma persistence_good_pair_relative_cohomology_bijective
    (K : Type) [Field K] [Algebra ℚ K]
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hclosed : IsClosedMap f) (A : Set Y) (hA : IsClosed A)
    (hfibre : ∀ y, y ∉ A → ∃! x, f x = y) (x : X) (hx : f x ∈ A)
    (UX : Set X) (hUX : IsOpen UX) (hBUX : f ⁻¹' A ⊆ UX)
    (qX : TopCat.of UX ⟶ TopCat.of (f ⁻¹' A))
    (hqX : persistenceSubsetNeighbourhoodInclusion (f ⁻¹' A) UX hBUX ≫ qX =
      𝟙 (TopCat.of (f ⁻¹' A)))
    (HX : TopCat.Homotopy (𝟙 (TopCat.of UX))
      (qX ≫ persistenceSubsetNeighbourhoodInclusion (f ⁻¹' A) UX hBUX))
    (hpresX : ∀ (t : unitInterval) (u : UX), f u.val ∈ A → f (HX (t, u)).val ∈ A)
    (UY : Set Y) (hUY : IsOpen UY) (hAUY : A ⊆ UY)
    (qY : TopCat.of UY ⟶ TopCat.of A)
    (hqY : persistenceSubsetNeighbourhoodInclusion A UY hAUY ≫ qY = 𝟙 (TopCat.of A))
    (HY : TopCat.Homotopy (𝟙 (TopCat.of UY))
      (qY ≫ persistenceSubsetNeighbourhoodInclusion A UY hAUY))
    (hpresY : ∀ (t : unitInterval) (u : UY), u.val ∈ A → (HY (t, u)).val ∈ A)
    (n : ℕ) :
    Function.Bijective (relativeCohomologyMap K n (persistencePairMap (TopCat.ofHom f) A)) := by
  have hsource := persistence_good_pair_collapse_relative_cohomology_bijective K
    (f ⁻¹' A) UX (hA.preimage f.continuous) hUX hBUX qX hqX HX hpresX x hx n
  have htarget := persistence_good_pair_collapse_relative_cohomology_bijective K
    A UY hA hUY hAUY qY hqY HY hpresY (f x) hx n
  have hcollapse := persistence_collapse_map_isHomeomorph f f.continuous hclosed A hA
    ⟨x, hx⟩ hfibre
  have hmiddle := persistence_point_pair_relative_cohomology_bijective K
    (TopCat.ofHom (persistenceCollapseContinuousMap f f.continuous A)) hcollapse
    (Quotient.mk (persistenceCollapseSetoid (f ⁻¹' A)) x) n
  have heq := congrArg (relativeCohomologyMap K n)
    (persistence_good_pair_quotient_square f A x hx)
  rw [relativeCohomologyMap_comp, relativeCohomologyMap_comp] at heq
  have hb : Function.Bijective
      ((relativeCohomologyMap K n (persistencePairMap (TopCat.ofHom f) A)) ∘
        (relativeCohomologyMap K n (persistenceCollapseLocusPairMap A (f x) hx))) := by
    change Function.Bijective
      ((relativeCohomologyMap K n (persistencePairMap (TopCat.ofHom f) A)) ∘ₗ
        (relativeCohomologyMap K n (persistenceCollapseLocusPairMap A (f x) hx)))
    rw [heq]
    exact hsource.comp hmiddle
  exact (Function.Bijective.of_comp_iff _ htarget).mp hb

end HodgeLean.Foundations.QuotientDuality
