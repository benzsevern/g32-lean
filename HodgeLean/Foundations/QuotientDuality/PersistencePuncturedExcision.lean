import HodgeLean.Foundations.QuotientDuality.PersistenceExcision
import HodgeLean.Foundations.QuotientDuality.PersistenceSubsetPairs

/-! Excision of the actual locus from an enlarged neighbourhood pair. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HomologicalComplex
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal inclusion of the punctured neighbourhood pair into the enlarged pair. -/
def persistencePuncturedNeighbourhoodPairMap
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    TopPair.ofSubset (X := TopCat.of ↥(Aᶜ : Set X)) {x | x.val ∈ U} ⟶
      TopPair.ofSubset (X := TopCat.of X) U :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of ↥(Aᶜ : Set X) ⟶ TopCat.of X)
    (fun _ hx => hx)

lemma persistence_punctured_neighbourhood_relative_chain_quasiIso
    (K : Type) [CommRing K] [Algebra ℚ K] {X : Type} [TopologicalSpace X]
    {A U : Set X} (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) :
    QuasiIso ((relativeChainFunctor K).map (persistencePuncturedNeighbourhoodPairMap A U)) := by
  have hcomp : Uᶜ ⊆ Aᶜ := by
    intro x hx hxa
    exact hx (hAU hxa)
  have h := persistence_support_excision_relative_chain_quasiIso K
    hA.isOpen_compl hU.isClosed_compl hcomp
  have hs : {x : ↥(Aᶜ : Set X) | x.val ∉ Uᶜ} =
      {x : ↥(Aᶜ : Set X) | x.val ∈ U} := by
    ext x
    exact not_not
  let eS := persistenceSubsetPairIso (TopCat.of ↥(Aᶜ : Set X)) _ _ hs
  let eT := persistenceSubsetPairIso (TopCat.of X) ((Uᶜ)ᶜ) U (compl_compl U)
  have hmap : persistencePuncturedNeighbourhoodPairMap A U =
      eS.inv ≫ persistenceSupportExcisionMap Aᶜ Uᶜ ≫ eT.hom := by
    apply persistence_pair_hom_ext
    change (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of ↥(Aᶜ : Set X) ⟶ TopCat.of X) =
      (𝟙 _) ≫ (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) ≫ (𝟙 _)
    simp only [Category.id_comp, Category.comp_id]
  letI := h
  rw [hmap, Functor.map_comp, Functor.map_comp]
  infer_instance

lemma persistence_punctured_neighbourhood_relative_cohomology_bijective
    (K : Type) [Field K] [Algebra ℚ K] {X : Type} [TopologicalSpace X]
    {A U : Set X} (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) (n : ℕ) :
    Function.Bijective
      (relativeCohomologyMap K n (persistencePuncturedNeighbourhoodPairMap A U)) := by
  exact persistence_relative_cohomology_bijective_of_relative_chain_quasiIso K _
    (persistence_punctured_neighbourhood_relative_chain_quasiIso K hA hU hAU) n

end HodgeLean.Foundations.QuotientDuality
