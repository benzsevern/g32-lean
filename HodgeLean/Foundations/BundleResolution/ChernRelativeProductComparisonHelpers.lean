import HodgeLean.Foundations.BundleResolution.ChernRelativeProductPairHelpers
import HodgeLean.Foundations.BundleResolution.ChernTensorCokernelHelpers
import HodgeLean.Foundations.BundleThom.RelativeChainQuasiIsoHelpers
import HodgeLean.Foundations.Singular.ProductHomotopyEquivalence

/-! # The actual relative Alexander–Whitney chain comparison

The natural absolute comparison descends through actual relative cokernels,
then uses the checked tensor cokernel identification.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits MonoidalCategory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

def i1_relativeProductAlexanderWhitney (P : TopPair) (Y : TopCat) :
    (relativeChainFunctor ℚ).obj (i1_relativeProductPair P Y) ⟶
      HomologicalComplex.tensorObj ((relativeChainFunctor ℚ).obj P) (rationalChains Y) := by
  letI : Mono (rationalChainMap P.map) := relativeChainMap_mono ℚ P
  exact (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map (i1_relativeProductAWArrow P Y) ≫
    (i1_tensorRightCokernelIso (rationalChainMap P.map) (rationalChains Y)).hom

theorem i1_relativeProductAlexanderWhitney_quasiIso (P : TopPair) (Y : TopCat) :
    QuasiIso (i1_relativeProductAlexanderWhitney P Y) := by
  letI : Mono (rationalChainMap P.map) := relativeChainMap_mono ℚ P
  letI : Mono (rationalChainMap P.map ▷ rationalChains Y) :=
    i1_tensorRight_mono (rationalChainMap P.map) (rationalChains Y)
  letI : Mono (Arrow.mk (rationalChainMap P.map ▷ rationalChains Y)).hom := by
    change Mono (rationalChainMap P.map ▷ rationalChains Y)
    infer_instance
  letI := relativeChainMap_mono ℚ (i1_relativeProductPair P Y)
  have hl : QuasiIso (i1_relativeProductAWArrow P Y).left :=
    (rationalProductTensorHomotopyEquiv P.snd Y).quasiIso_inv
  have hr : QuasiIso (i1_relativeProductAWArrow P Y).right :=
    (rationalProductTensorHomotopyEquiv P.fst Y).quasiIso_inv
  letI := i1_chainArrowCokernelMap_quasiIso (i1_relativeProductAWArrow P Y) hl hr
  unfold i1_relativeProductAlexanderWhitney
  infer_instance

theorem i1_relativeProductAlexanderWhitney_projection (P : TopPair) (Y : TopCat) :
    relativeChainProjection ℚ (i1_relativeProductPair P Y) ≫
        i1_relativeProductAlexanderWhitney P Y =
      productAlexanderWhitney P.fst Y ≫ (relativeChainProjection ℚ P ▷ rationalChains Y) := by
  letI : Mono (rationalChainMap P.map) := relativeChainMap_mono ℚ P
  change cokernel.π ((chainPairFunctor ℚ).obj (i1_relativeProductPair P Y)).hom ≫
    ((coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map (i1_relativeProductAWArrow P Y) ≫
      (i1_tensorRightCokernelIso (rationalChainMap P.map) (rationalChains Y)).hom) = _
  have h : cokernel.π ((chainPairFunctor ℚ).obj (i1_relativeProductPair P Y)).hom ≫
      (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map (i1_relativeProductAWArrow P Y) =
    productAlexanderWhitney P.fst Y ≫ cokernel.π (rationalChainMap P.map ▷ rationalChains Y) :=
    ((coker.π (ChainComplex (ModuleCat ℚ) ℕ)).naturality (i1_relativeProductAWArrow P Y)).symm
  rw [← Category.assoc, h, Category.assoc, i1_tensorRightCokernelIso_π]
  rfl

end HodgeLean.Foundations.BundleResolution
