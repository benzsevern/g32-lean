import HodgeLean.Foundations.QuotientDuality.PersistenceCollapseChainComparison
import HodgeLean.Foundations.QuotientDuality.PersistenceNestedTripleLift

/-! Actual enlargement composition and quotient squares in the comparison argument. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_subset_enlargement_comp
    {X : Type} [TopologicalSpace X] (A M N : Set X) (hAM : A ⊆ M) (hMN : M ⊆ N) :
    persistenceSubsetEnlargementMap A M hAM ≫ persistenceSubsetEnlargementMap M N hMN =
      persistenceSubsetEnlargementMap A N (hAM.trans hMN) := by
  apply persistence_pair_hom_ext
  exact Category.id_comp _

lemma persistence_collapse_neighbourhood_enlargement_square
    {X : Type} [TopologicalSpace X] (A M N : Set X) (hMN : M ⊆ N) :
    persistenceSubsetEnlargementMap M N hMN ≫ persistenceCollapseNeighbourhoodPairMap A N =
      persistenceCollapseNeighbourhoodPairMap A M ≫ persistenceSubsetEnlargementMap
        ((Quotient.mk (persistenceCollapseSetoid A)) '' M)
        ((Quotient.mk (persistenceCollapseSetoid A)) '' N) (Set.image_mono hMN) := by
  apply persistence_pair_hom_ext
  apply TopCat.ext
  intro x
  rfl

end HodgeLean.Foundations.QuotientDuality
