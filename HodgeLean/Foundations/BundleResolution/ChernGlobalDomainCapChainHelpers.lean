import HodgeLean.Foundations.BundleResolution.ChernDomainCapNaturalityHelpers

/-! # Actual global cap and its inverse-image domain restrictions

The global map caps by the supplied relative cocycle and then applies
the actual continuous projection to the base.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable (X Y : TopCat.{0}) (f : X ⟶ Y) (Z : Set X) (k : ℕ)
variable (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k))

def i1_globalEvenCapExtendedMap :
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) Z)).extend
        (ComplexShape.embeddingUpIntLE (2 * k : ℕ)) ⟶
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).obj Y).extend
        (ComplexShape.embeddingUpIntLE 0) :=
  i1_evenRelativeCapExtendedChainMap (TopPair.ofSubset (X := X) Z) k φ.val φ.property ≫
    HomologicalComplex.extendMap (singularChainComplexMap ℚ f) (ComplexShape.embeddingUpIntLE 0)

theorem i1_globalEvenCapExtendedMap_domain (U : Set Y) :
    HomologicalComplex.extendMap
        ((relativeChainFunctor ℚ).map (i1_subsetRelativePairInclusion X Z (f ⁻¹' U)))
        (ComplexShape.embeddingUpIntLE (2 * k : ℕ)) ≫
      i1_globalEvenCapExtendedMap X Y f Z k φ =
    i1_domainEvenCapExtendedMap X Y f Z U k φ ≫
      HomologicalComplex.extendMap (singularChainComplexMap ℚ (topologicalSubsetInclusion Y U))
        (ComplexShape.embeddingUpIntLE 0) := by
  let a := i1_subsetRelativePairInclusion X Z (f ⁻¹' U)
  have hc := i1_evenRelativeCapExtendedChainMap_naturality a k φ
  have he : HomologicalComplex.extendMap (singularChainComplexMap ℚ (TopPair.Hom.fst a))
        (ComplexShape.embeddingUpIntLE 0) ≫
        HomologicalComplex.extendMap (singularChainComplexMap ℚ f) (ComplexShape.embeddingUpIntLE 0) =
      HomologicalComplex.extendMap (singularChainComplexMap ℚ (i1_domainBaseProjection X Y f Z U))
          (ComplexShape.embeddingUpIntLE 0) ≫
        HomologicalComplex.extendMap (singularChainComplexMap ℚ (topologicalSubsetInclusion Y U))
          (ComplexShape.embeddingUpIntLE 0) := by
    rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
    apply congrArg (fun q => HomologicalComplex.extendMap q (ComplexShape.embeddingUpIntLE 0))
    let C : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
      (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
    change C.map (TopPair.Hom.fst a) ≫ C.map f =
      C.map (i1_domainBaseProjection X Y f Z U) ≫ C.map (topologicalSubsetInclusion Y U)
    rw [← C.map_comp, ← C.map_comp]
    rfl
  dsimp only [i1_globalEvenCapExtendedMap, i1_domainEvenCapExtendedMap]
  rw [← Category.assoc, hc, Category.assoc, he, Category.assoc]

end HodgeLean.Foundations.BundleResolution
