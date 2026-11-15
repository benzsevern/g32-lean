import HodgeLean.Foundations.QuotientDuality.LocalOpenEmbeddingPointHomology

/-! Composition of actual point-complement pair maps. -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem imagePointPairMap_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Function.Injective f) (hg : Function.Injective g) (x : X) :
    imagePointPairMap f hf x ≫ imagePointPairMap g hg (f x) =
      imagePointPairMap (f ≫ g) (hg.comp hf) x := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    rfl
  · ext z
    rfl

theorem point_homology_map_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Function.Injective f) (hg : Function.Injective g) (x : X) (n : ℕ)
    (c : orientationGroup X n x) :
    relativeHomologyMap ℚ n (imagePointPairMap g hg (f x))
      (relativeHomologyMap ℚ n (imagePointPairMap f hf x) c) =
        relativeHomologyMap ℚ n (imagePointPairMap (f ≫ g) (hg.comp hf) x) c := by
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, imagePointPairMap_comp]

#print axioms imagePointPairMap_comp
#print axioms point_homology_map_comp
end HodgeLean.Foundations.QuotientDuality
