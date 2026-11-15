import HodgeLean.Foundations.BundleResolution.ChernEvenCapChainHelpers
import HodgeLean.Foundations.BundleResolution.ChernCapChainNaturalityHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeClassNaturalityHelpers

/-! # Pair naturality of integer-extended even cap comparisons

The actual pair chain map and the actual absolute chain map form a square
with even cap and the pulled-back relative cocycle.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_evenRelativeCapExtendedChainMap_naturality {P Q : TopPair}
    (f : P ⟶ Q) (k : ℕ) (φ : RelativeCocycle ℚ Q (2 * k)) :
    HomologicalComplex.extendMap ((relativeChainFunctor ℚ).map f)
        (ComplexShape.embeddingUpIntLE (2 * k : ℕ)) ≫
      i1_evenRelativeCapExtendedChainMap Q k φ.val φ.property =
    i1_evenRelativeCapExtendedChainMap P k
        (i1_relativeCocyclePullback f (2 * k) φ).val
        (i1_relativeCocyclePullback f (2 * k) φ).property ≫
      HomologicalComplex.extendMap (singularChainComplexMap ℚ (TopPair.Hom.fst f))
        (ComplexShape.embeddingUpIntLE 0) := by
  dsimp only [i1_evenRelativeCapExtendedChainMap]
  apply i1_degreeLoweringExtendedChainMap_naturality
  intro n
  apply ModuleCat.hom_ext
  ext c
  exact (i1_relativeCap_chain_naturality f (2 * k) n φ.val c).symm

end HodgeLean.Foundations.BundleResolution
