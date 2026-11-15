import HodgeLean.Foundations.QuotientDuality.LocalChartEmbedding
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativePairExcision

/-! Local point-pair transport through an arbitrary open embedding. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : IsOpenEmbedding f) (x : X)

def openEmbeddingTargetPointPairIso :
    pointComplementPair x ≅ neighborhoodPointComplementPair (Set.range f) (f x) := by
  let H : X ≃ₜ Set.range f := hf.isEmbedding.toHomeomorph
  let Hp : ({x}ᶜ : Set X) ≃ₜ {y : Set.range f | y.val ≠ f x} :=
    H.subtype fun z => by
      change z ≠ x ↔ f z ≠ f x
      constructor
      · intro hz heq
        exact hz (hf.injective heq)
      · intro hz heq
        exact hz (congrArg f heq)
  exact {
    hom := TopPair.ofHom (TopCat.ofHom ⟨H, H.continuous⟩)
      (TopCat.ofHom ⟨Hp, Hp.continuous⟩) (by ext z; rfl)
    inv := TopPair.ofHom (TopCat.ofHom ⟨H.symm, H.symm.continuous⟩)
      (TopCat.ofHom ⟨Hp.symm, Hp.symm.continuous⟩) (by ext z; rfl)
    hom_inv_id := by
      apply MorphismProperty.Arrow.Hom.ext
      · ext z
        exact Hp.left_inv z
      · ext z
        exact H.left_inv z
    inv_hom_id := by
      apply MorphismProperty.Arrow.Hom.ext
      · ext z
        exact Hp.right_inv z
      · ext z
        exact H.right_inv z }

#print axioms openEmbeddingTargetPointPairIso
end HodgeLean.Foundations.QuotientDuality
