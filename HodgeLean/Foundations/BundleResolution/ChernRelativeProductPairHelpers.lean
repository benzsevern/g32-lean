import HodgeLean.Foundations.BundleResolution.ChernRelativeCupPullbackHelpers
import HodgeLean.Foundations.Singular.ProductAWComparison

/-! # Actual products of topological pairs with spaces

The product pair retains the actual embedded subspace, so its singular
quotient can be compared with tensor chains through Alexander–Whitney.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

def i1_relativeProductPair (P : TopPair) (Y : TopCat) : TopPair :=
  TopPair.of (topologicalProductMap P.map (𝟙 Y))
    ((TopPair.isEmbedding_map P).prodMap Topology.IsEmbedding.id)

def i1_relativeProductFirst (P : TopPair) (Y : TopCat) : i1_relativeProductPair P Y ⟶ P :=
  TopPair.ofHom (productFirst P.fst Y) (productFirst P.snd Y) (by ext z; rfl)

def i1_relativeProductAWArrow (P : TopPair) (Y : TopCat) :
    (chainPairFunctor ℚ).obj (i1_relativeProductPair P Y) ⟶
      Arrow.mk (rationalChainMap P.map ▷ rationalChains Y) :=
  Arrow.homMk (productAlexanderWhitney P.snd Y) (productAlexanderWhitney P.fst Y) (by
    have h := productAlexanderWhitney_naturality P.map (𝟙 Y)
    have hi : rationalChainMap (𝟙 Y) = 𝟙 (rationalChains Y) :=
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ))).map_id Y
    change rationalChainMap (topologicalProductMap P.map (𝟙 Y)) ≫
      productAlexanderWhitney P.fst Y = productAlexanderWhitney P.snd Y ≫
        HomologicalComplex.tensorHom (rationalChainMap P.map) (rationalChainMap (𝟙 Y)) at h
    rw [hi] at h
    exact h.symm)

end HodgeLean.Foundations.BundleResolution
