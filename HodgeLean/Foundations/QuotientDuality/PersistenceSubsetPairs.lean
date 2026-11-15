import HodgeLean.Foundations.QuotientDuality.PersistencePairSequence

/-! Identity ambient maps between equal subspace presentations. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

/-- Equal subsets give a pair isomorphism with the literal identity ambient maps. -/
def persistenceSubsetPairIso (X : TopCat.{0}) (A B : Set X) (h : A = B) :
    TopPair.ofSubset A ≅ TopPair.ofSubset B where
  hom := TopPair.ofSubsetHom (𝟙 X) (by
    intro x hx
    change x ∈ B
    rw [← h]
    exact hx)
  inv := TopPair.ofSubsetHom (𝟙 X) (by
    intro x hx
    change x ∈ A
    rw [h]
    exact hx)
  hom_inv_id := by
    apply persistence_pair_hom_ext
    exact Category.id_comp _
  inv_hom_id := by
    apply persistence_pair_hom_ext
    exact Category.id_comp _

end HodgeLean.Foundations.QuotientDuality
