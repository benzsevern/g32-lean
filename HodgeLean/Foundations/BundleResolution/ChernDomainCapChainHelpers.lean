import HodgeLean.Foundations.BundleResolution.ChernEvenCapNaturalityHelpers
import HodgeLean.Foundations.BundleResolution.ChernCocyclePullbackCompositionHelpers
import HodgeLean.Foundations.BundleThom.SubsetRelativeCoclassNaturalityHelpers

/-! # Actual even cap chain comparisons on inverse-image domains

A continuous projection and one actual relative cocycle give compatible
local chain maps to the actual base domains.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

variable (X Y : TopCat.{0}) (f : X ⟶ Y) (Z : Set X) (U : Set Y)

def i1_domainBaseProjection :
    (i1_subsetRelativePair X Z (f ⁻¹' U)).fst ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun v => ⟨f v.val, v.property⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

def i1_domainEvenCapExtendedMap (k : ℕ)
    (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k)) :
    ((relativeChainFunctor ℚ).obj (i1_subsetRelativePair X Z (f ⁻¹' U))).extend
        (ComplexShape.embeddingUpIntLE (2 * k : ℕ)) ⟶
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).obj
        (TopCat.of U)).extend (ComplexShape.embeddingUpIntLE 0) :=
  i1_evenRelativeCapExtendedChainMap (i1_subsetRelativePair X Z (f ⁻¹' U)) k
      (i1_relativeCocyclePullback (i1_subsetRelativePairInclusion X Z (f ⁻¹' U))
        (2 * k) φ).val
      (i1_relativeCocyclePullback (i1_subsetRelativePairInclusion X Z (f ⁻¹' U))
        (2 * k) φ).property ≫
    HomologicalComplex.extendMap
      (singularChainComplexMap ℚ (i1_domainBaseProjection X Y f Z U))
      (ComplexShape.embeddingUpIntLE 0)

end HodgeLean.Foundations.BundleResolution
