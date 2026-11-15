import HodgeLean.Foundations.BundleResolution.ChernRelativeProductCupCochainHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeProductCohomologyHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeCupCocycleHelpers
import HodgeLean.Foundations.BundleResolution.ChernDualCycleNaturalityHelpers
import HodgeLean.Foundations.Singular.SingularCocyclePullback
import HodgeLean.Foundations.Singular.TensorScalarCycle

/-! # Relative product cohomology on represented tensor classes

The actual relative product comparison sends a represented scalar tensor
class to relative cup multiplication of the actual coordinate pullbacks.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.Singular HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

theorem i1_relativeTensorScalarCycle_AW_class (P : TopPair) (Y : TopCat) (p q : ℕ)
    (φ : RelativeCocycle ℚ P p) (ψ : Cocycle ℚ (TopCat.toSSet.obj Y) q) :
    i1_relativeProductTensorCohomologyEquiv P Y (p + q)
      (((HomologicalComplex.tensorObj ((relativeChainFunctor ℚ).obj P) (rationalChains Y)).sc
        (p + q)).linearDual.moduleCatHomologyClass
          (tensorScalarCycle ((relativeChainFunctor ℚ).obj P) (rationalChains Y) p q
            (i1_relativeCocycleToDualCycle P p φ) (i1_cocycleToDualCycle Y q ψ))) =
      i1_relativeCup (i1_relativeProductPair P Y) p q
        (relativeCohomologyMap ℚ p (i1_relativeProductFirst P Y) (i1_relativeCocycleClass P p φ))
        (cohomologyMap ℚ q (productSecond P.fst Y) (cohomologyClass Y q ψ)) := by
  let t := tensorScalarCycle ((relativeChainFunctor ℚ).obj P) (rationalChains Y) p q
    (i1_relativeCocycleToDualCycle P p φ) (i1_cocycleToDualCycle Y q ψ)
  change i1_chainDualPullback (p + q) (i1_relativeProductAlexanderWhitney P Y)
    (i1_chainDualCycleClass
      (HomologicalComplex.tensorObj ((relativeChainFunctor ℚ).obj P) (rationalChains Y)) (p + q) t) = _
  rw [i1_chainDualPullback_class]
  let ψp := singularCocyclePullback (productSecond P.fst Y) q ψ
  rw [i1_relativeCohomologyMap_class,
    cohomologyMap_class Y (productSecond P.fst Y) q ψ ψp rfl]
  have hc := i1_relativeCup_on_class (i1_relativeProductPair P Y) p q
    (i1_relativeCocyclePullback (i1_relativeProductFirst P Y) p φ) ψp
  refine Eq.trans ?_ hc.symm
  apply congrArg (i1_chainDualCycleClass
    ((relativeChainFunctor ℚ).obj (i1_relativeProductPair P Y)) (p + q))
  apply Subtype.ext
  exact i1_relativeTensorScalarCochain_AW P Y p q φ.val ψ.val

end HodgeLean.Foundations.BundleResolution
