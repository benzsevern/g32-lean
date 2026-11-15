import HodgeLean.Foundations.QuotientDuality.PersistenceCollapseExcision
import HodgeLean.Foundations.QuotientDuality.PersistenceImageContraction
import HodgeLean.Foundations.QuotientDuality.PersistenceSubsetEnlargement

/-! The literal quotient map from a deformation-neighbourhood pair. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal quotient projection from the locus pair to its specified collapsed point. -/
def persistenceCollapseLocusPairMap
    {X : Type} [TopologicalSpace X] (A : Set X) (a : X) (ha : a ∈ A) :
    TopPair.ofSubset (X := TopCat.of X) A ⟶
      TopPair.ofSubset (X := TopCat.of (Quotient (persistenceCollapseSetoid A)))
        {Quotient.mk (persistenceCollapseSetoid A) a} :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨Quotient.mk (persistenceCollapseSetoid A), continuous_quotient_mk'⟩)
    (fun x hx => Quotient.sound (Or.inr ⟨hx, ha⟩))

lemma persistence_collapse_enlargement_square
    {X : Type} [TopologicalSpace X] (A U : Set X) (hAU : A ⊆ U)
    (a : X) (ha : a ∈ A) :
    persistenceSubsetEnlargementMap A U hAU ≫
      persistenceCollapseNeighbourhoodPairMap A U =
    persistenceCollapseLocusPairMap A a ha ≫
      persistenceSubsetEnlargementMap
        ({Quotient.mk (persistenceCollapseSetoid A) a})
        ((Quotient.mk (persistenceCollapseSetoid A)) '' U) (by
          intro y hy
          rcases Set.mem_singleton_iff.mp hy with rfl
          exact ⟨a, hAU ha, rfl⟩) := by
  apply persistence_pair_hom_ext
  rfl

lemma persistence_good_pair_collapse_relative_cohomology_bijective
    (K : Type) [Field K] [Algebra ℚ K] {X : Type} [TopologicalSpace X]
    (A U : Set X) (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U)
    (q : TopCat.of U ⟶ TopCat.of A)
    (hq : persistenceSubsetNeighbourhoodInclusion A U hAU ≫ q = 𝟙 (TopCat.of A))
    (H : TopCat.Homotopy (𝟙 (TopCat.of U))
      (q ≫ persistenceSubsetNeighbourhoodInclusion A U hAU))
    (hpres : ∀ (t : unitInterval) (u : U), u.val ∈ A → (H (t, u)).val ∈ A)
    (a : X) (ha : a ∈ A) (n : ℕ) :
    Function.Bijective (relativeCohomologyMap K n (persistenceCollapseLocusPairMap A a ha)) := by
  let j := persistenceSubsetNeighbourhoodInclusion A U hAU
  let aU : U := ⟨a, hAU ha⟩
  let c := Quotient.mk (persistenceCollapseSetoid A)
  have haV : c a ∈ c '' U := ⟨a, hAU ha, rfl⟩
  let Himage := persistenceCollapseImageContraction A U hA hAU (q ≫ j).hom H hpres
    (fun u => (q u).property) aU ha
  have hsource := persistence_subset_enlargement_relative_cohomology_bijective K
    A U hAU q hq H n
  have hlarge := persistence_collapse_neighbourhood_relative_cohomology_bijective K
    A U hA hU hAU n
  have htarget := persistence_singleton_enlargement_relative_cohomology_bijective K
    (c '' U) (c a) haV Himage n
  have heq := congrArg (relativeCohomologyMap K n)
    (persistence_collapse_enlargement_square A U hAU a ha)
  rw [relativeCohomologyMap_comp, relativeCohomologyMap_comp] at heq
  have hb : Function.Bijective
      ((relativeCohomologyMap K n (persistenceCollapseLocusPairMap A a ha)) ∘
        (relativeCohomologyMap K n (persistenceSubsetEnlargementMap {c a} (c '' U) (by
          intro y hy
          rcases Set.mem_singleton_iff.mp hy with rfl
          exact haV)))) := by
    change Function.Bijective
      ((relativeCohomologyMap K n (persistenceCollapseLocusPairMap A a ha)) ∘ₗ
        (relativeCohomologyMap K n (persistenceSubsetEnlargementMap {c a} (c '' U) _)))
    rw [← heq]
    exact hsource.comp hlarge
  exact (Function.Bijective.of_comp_iff _ htarget).mp hb

lemma persistence_good_pair_collapse_relative_cohomology_bijective_of_fixed
    (K : Type) [Field K] [Algebra ℚ K] {X : Type} [TopologicalSpace X]
    (A U : Set X) (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U)
    (q : TopCat.of U ⟶ TopCat.of A)
    (hq : persistenceSubsetNeighbourhoodInclusion A U hAU ≫ q = 𝟙 (TopCat.of A))
    (H : TopCat.Homotopy (𝟙 (TopCat.of U))
      (q ≫ persistenceSubsetNeighbourhoodInclusion A U hAU))
    (hfixed : ∀ (t : unitInterval) (a : A),
      H (t, persistenceSubsetNeighbourhoodInclusion A U hAU a) =
        persistenceSubsetNeighbourhoodInclusion A U hAU a)
    (a : X) (ha : a ∈ A) (n : ℕ) :
    Function.Bijective (relativeCohomologyMap K n (persistenceCollapseLocusPairMap A a ha)) := by
  apply persistence_good_pair_collapse_relative_cohomology_bijective K
    A U hA hU hAU q hq H _ a ha n
  intro t u hu
  have heq := hfixed t (⟨u.val, hu⟩ : A)
  have heq' : H (t, u) = u := heq
  rw [heq']
  exact hu

end HodgeLean.Foundations.QuotientDuality
