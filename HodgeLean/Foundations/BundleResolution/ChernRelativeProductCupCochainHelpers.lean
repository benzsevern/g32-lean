import HodgeLean.Foundations.BundleResolution.ChernRelativeProductComparisonHelpers
import HodgeLean.Foundations.BundleResolution.ChernTensorScalarNaturalityHelpers
import HodgeLean.Foundations.Singular.ProductTensorCupCochain

/-! # Actual relative cross cochains and cup multiplication

The actual relative Alexander–Whitney comparison sends the scalar tensor
cochain to the relative cup of the two actual coordinate pullbacks.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_relativeTensorScalarCochain_AW (P : TopPair) (Y : TopCat) (p q : ℕ)
    (φ : RelativeCochain ℚ P p) (ψ : Cochain ℚ (TopCat.toSSet.obj Y) q) :
    (tensorScalarCochain ((relativeChainFunctor ℚ).obj P) (rationalChains Y) p q φ ψ).comp
        ((i1_relativeProductAlexanderWhitney P Y).f (p + q)).hom =
      i1_relativeCupCochain (i1_relativeProductPair P Y) p q
        (i1_relativeCochainPullback (i1_relativeProductFirst P Y) p φ)
        (cochainMap ℚ (TopCat.toSSet.map (productSecond P.fst Y)) q ψ) := by
  apply i1_relativeCochainToAbsolute_injective (i1_relativeProductPair P Y) (p + q)
  rw [i1_relativeCupCochain_toAbsolute, i1_relativeCochainPullback_toAbsolute]
  ext c
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f (p + q)) (i1_relativeProductAlexanderWhitney_projection P Y)) c
  change ((i1_relativeProductAlexanderWhitney P Y).f (p + q)).hom
      (((relativeChainProjection ℚ (i1_relativeProductPair P Y)).f (p + q)).hom c) =
    ((relativeChainProjection ℚ P ▷ rationalChains Y).f (p + q)).hom
      (((productAlexanderWhitney P.fst Y).f (p + q)).hom c) at h
  change tensorScalarCochain ((relativeChainFunctor ℚ).obj P) (rationalChains Y) p q φ ψ
      (((i1_relativeProductAlexanderWhitney P Y).f (p + q)).hom
        (((relativeChainProjection ℚ (i1_relativeProductPair P Y)).f (p + q)).hom c)) = _
  rw [h]
  have hn := LinearMap.congr_fun
    (i1_tensorScalarCochain_mapLeft (relativeChainProjection ℚ P) (rationalChains Y) p q φ ψ)
    (((productAlexanderWhitney P.fst Y).f (p + q)).hom c)
  exact hn.trans (LinearMap.congr_fun (tensorScalarCochain_AW P.fst Y p q
    (relativeCochainToAbsolute ℚ P p φ) ψ) c)

end HodgeLean.Foundations.BundleResolution
