import HodgeLean.Foundations.BundleResolution.ChernRelativeCocycleClassHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeCupNaturalityHelpers

/-! # Actual relative cocycle classes under pair pullback

Pulling back an actual relative cocycle represents the standard relative
cohomology pullback on its class.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory HomologicalComplex AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleResolution

variable {P Q : TopPair} (f : P ⟶ Q) (n : ℕ)

def i1_relativeCocyclePullback (φ : RelativeCocycle ℚ Q n) : RelativeCocycle ℚ P n :=
  ⟨i1_relativeCochainPullback f n φ.val, by
    change relativeCoboundary ℚ P n (i1_relativeCochainPullback f n φ.val) = 0
    rw [← i1_relativeCochainPullback_coboundary, φ.property, map_zero]⟩

set_option backward.isDefEq.respectTransparency false in
theorem i1_relativeCohomologyMap_class (φ : RelativeCocycle ℚ Q n) :
    relativeCohomologyMap ℚ n f (i1_relativeCocycleClass Q n φ) =
      i1_relativeCocycleClass P n (i1_relativeCocyclePullback f n φ) := by
  apply (relativeCohomologyEquivDualHomology ℚ P n).injective
  ext z
  obtain ⟨z, rfl⟩ := (((relativeChainFunctor ℚ).obj P).sc n).moduleCatHomologyClass_surjective z
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    i1_relativeCocycleClass_pairing]
  let g := (shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map
    ((relativeChainFunctor ℚ).map f)
  change relativeCohomologyEquivDualHomology ℚ Q n (i1_relativeCocycleClass Q n φ)
    ((ShortComplex.homologyMap g).hom
      ((((relativeChainFunctor ℚ).obj P).sc n).moduleCatHomologyClass z)) = _
  rw [ShortComplex.moduleCatHomologyClass_naturality, i1_relativeCocycleClass_pairing]
  rfl

end HodgeLean.Foundations.BundleResolution
