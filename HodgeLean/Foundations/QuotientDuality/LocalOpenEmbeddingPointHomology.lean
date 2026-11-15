import HodgeLean.Foundations.QuotientDuality.LocalOpenEmbeddingPointIso

/-! Excision makes the point-local map of an open embedding bijective. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : IsOpenEmbedding f) (x : X)

theorem openEmbeddingTargetPointPairIso_comp :
    (openEmbeddingTargetPointPairIso f hf x).hom ≫
      neighborhoodPointComplementPairMap (Set.range f) (f x) =
        imagePointPairMap f hf.injective x := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    rfl
  · ext z
    rfl

theorem openEmbedding_point_homology_bijective [T1Space Y] (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n (imagePointPairMap f hf.injective x)) := by
  have he : Function.Bijective
      (relativeHomologyMap ℚ n (openEmbeddingTargetPointPairIso f hf x).hom) :=
    (ConcreteCategory.isIso_iff_bijective
      ((relativeHomologyFunctor ℚ n).map (openEmbeddingTargetPointPairIso f hf x).hom)).mp inferInstance
  have hn := neighborhoodPointComplement_relativeHomologyMap_bijective
    (Set.range f) (f x) hf.isOpen_range ⟨x, rfl⟩ n
  rw [← openEmbeddingTargetPointPairIso_comp f hf x, relativeHomologyMap_comp]
  exact hn.comp he

#print axioms openEmbeddingTargetPointPairIso_comp
#print axioms openEmbedding_point_homology_bijective
end HodgeLean.Foundations.QuotientDuality
