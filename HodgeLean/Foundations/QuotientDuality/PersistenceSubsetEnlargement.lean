import HodgeLean.Foundations.QuotientDuality.PersistenceNeighbourhoodEnlargement

/-! Enlargement on literal subset pairs with their specified neighbourhood retractions. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal inclusion of a subset into its specified neighbourhood. -/
def persistenceSubsetNeighbourhoodInclusion
    {X : Type} [TopologicalSpace X] (A U : Set X) (hAU : A ⊆ U) :
    TopCat.of A ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun a => ⟨a.val, hAU a.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The literal identity ambient map enlarging the subset in a pair. -/
def persistenceSubsetEnlargementMap
    {X : Type} [TopologicalSpace X] (A U : Set X) (hAU : A ⊆ U) :
    TopPair.ofSubset (X := TopCat.of X) A ⟶ TopPair.ofSubset (X := TopCat.of X) U :=
  TopPair.ofSubsetHom (𝟙 (TopCat.of X)) (fun _ hx => hAU hx)

lemma persistence_subset_enlargement_relative_cohomology_bijective
    (K : Type) [Field K] {X : Type} [TopologicalSpace X]
    (A U : Set X) (hAU : A ⊆ U) (q : TopCat.of U ⟶ TopCat.of A)
    (hq : persistenceSubsetNeighbourhoodInclusion A U hAU ≫ q = 𝟙 (TopCat.of A))
    (H : TopCat.Homotopy (𝟙 (TopCat.of U))
      (q ≫ persistenceSubsetNeighbourhoodInclusion A U hAU)) (n : ℕ) :
    Function.Bijective
      (relativeCohomologyMap K n (persistenceSubsetEnlargementMap A U hAU)) := by
  let k : TopCat.of U ⟶ TopCat.of X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hfactor : persistenceSubsetNeighbourhoodInclusion A U hAU ≫ k =
      (TopPair.ofSubset (X := TopCat.of X) A).map := rfl
  have hmap : persistenceSubsetEnlargementMap A U hAU =
      persistenceNeighbourhoodEnlargement (TopPair.ofSubset (X := TopCat.of X) A)
        (TopCat.of U) (persistenceSubsetNeighbourhoodInclusion A U hAU) k hfactor
        Topology.IsEmbedding.subtypeVal := by
    apply persistence_pair_hom_ext
    rfl
  rw [hmap]
  exact persistence_neighbourhood_enlargement_relative_cohomology_bijective K _ _ _ _
    hfactor Topology.IsEmbedding.subtypeVal q hq H n

lemma persistence_singleton_enlargement_relative_cohomology_bijective
    (K : Type) [Field K] {X : Type} [TopologicalSpace X]
    (U : Set X) (a : X) (haU : a ∈ U)
    (H : ContinuousMap.Homotopy (ContinuousMap.id U)
      (ContinuousMap.const U (⟨a, haU⟩ : U))) (n : ℕ) :
    Function.Bijective (relativeCohomologyMap K n
      (persistenceSubsetEnlargementMap ({a} : Set X) U (by
        intro x hx
        rcases Set.mem_singleton_iff.mp hx with rfl
        exact haU))) := by
  let hAU : ({a} : Set X) ⊆ U := by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact haU
  let q : TopCat.of U ⟶ TopCat.of ({a} : Set X) :=
    TopCat.ofHom (ContinuousMap.const U (⟨a, rfl⟩ : ({a} : Set X)))
  apply persistence_subset_enlargement_relative_cohomology_bijective K _ _ hAU q _ H n
  apply TopCat.ext
  intro y
  apply Subtype.ext
  exact (Set.mem_singleton_iff.mp y.property).symm

end HodgeLean.Foundations.QuotientDuality
