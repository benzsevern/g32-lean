import HodgeLean.Foundations.QuotientDuality.PersistencePairSequence
import Mathlib.Topology.Homeomorph.Lemmas

/-! Actual changes from embedded subspaces to their literal image subsets. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

/-- Replace an embedded subspace by its actual image while retaining the identity ambient maps. -/
def persistenceEmbeddedPairImageIso
    {A X : TopCat.{0}} (f : A ⟶ X) (hf : Topology.IsEmbedding f) :
    TopPair.of f hf ≅ TopPair.ofSubset (Set.range f) := by
  let e := hf.toHomeomorph
  exact {
    hom := TopPair.ofHom (𝟙 X) (TopCat.ofHom ⟨e, e.continuous⟩) (by
      apply TopCat.ext
      intro a
      rfl)
    inv := TopPair.ofHom (𝟙 X) (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) (by
      apply TopCat.ext
      intro a
      exact congrArg Subtype.val (e.apply_symm_apply a))
    hom_inv_id := by
      apply persistence_pair_hom_ext
      exact Category.id_comp _
    inv_hom_id := by
      apply persistence_pair_hom_ext
      exact Category.id_comp _ }

end HodgeLean.Foundations.QuotientDuality
