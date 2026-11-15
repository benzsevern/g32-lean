import HodgeLean.Foundations.BundleResolution.ChernDualCycleClassHelpers
import HodgeLean.Foundations.BundleThom.ChainDualPullbackHelpers

/-! # Actual dual-cycle classes under chain pullback

The standard dual-chain class map commutes with the actual chain map
on cycle representatives.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

theorem i1_chainDualPullback_class {K L : ChainComplex (ModuleCat ℚ) ℕ}
    (f : K ⟶ L) (n : ℕ) (φ : LinearMap.ker (L.sc n).f.hom.dualMap) :
    i1_chainDualPullback n f (i1_chainDualCycleClass L n φ) =
      i1_chainDualCycleClass K n (ShortComplex.moduleCatCycleMap
        (ShortComplex.linearDualMap
          ((shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map f)) φ) := by
  apply (K.linearDualHomologyEquiv n).injective
  ext z
  obtain ⟨z, rfl⟩ := (K.sc n).moduleCatHomologyClass_surjective z
  rw [i1_chainDualPullback_pairing, i1_chainDualCycleClass_pairing]
  change L.linearDualHomologyEquiv n (i1_chainDualCycleClass L n φ)
    ((ShortComplex.homologyMap
      ((shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map f)).hom
        ((K.sc n).moduleCatHomologyClass z)) = _
  rw [ShortComplex.moduleCatHomologyClass_naturality, i1_chainDualCycleClass_pairing]
  rfl

end HodgeLean.Foundations.BundleResolution
