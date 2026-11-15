import HodgeLean.Foundations.BundleResolution.ChernRelativeCocycleClassHelpers
import HodgeLean.Foundations.BundleResolution.ChernCocyclePairingHelpers

/-! # Forgetting support on cocycle representatives

The standard relative-to-absolute map pulls a relative cocycle back along
the actual relative chain projection.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory HomologicalComplex AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

variable (P : TopPair) (n : ℕ)

def i1_relativeCocycleToAbsolute (φ : RelativeCocycle ℚ P n) :
    Cocycle ℚ (TopCat.toSSet.obj P.fst) n :=
  ⟨relativeCochainToAbsolute ℚ P n φ.val, by
    change coboundary ℚ n (relativeCochainToAbsolute ℚ P n φ.val) = 0
    rw [← relativeCochainToAbsolute_coboundary, φ.property, map_zero]⟩

set_option backward.isDefEq.respectTransparency false in
theorem i1_relativeCocycleClass_toAbsolute (φ : RelativeCocycle ℚ P n) :
    relativeCohomologyToAbsolute ℚ P n (i1_relativeCocycleClass P n φ) =
      cohomologyClass P.fst n (i1_relativeCocycleToAbsolute P n φ) := by
  apply (cohomologyEquivDualHomology ℚ P.fst n).injective
  ext z
  obtain ⟨z, rfl⟩ := ((SingularChainComplex ℚ P.fst).sc n).moduleCatHomologyClass_surjective z
  rw [cohomologyEquivDualHomology_relativeCohomologyToAbsolute, i1_cohomologyClass_pairing]
  let f := (shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map
    (relativeChainProjection ℚ P)
  change relativeCohomologyEquivDualHomology ℚ P n (i1_relativeCocycleClass P n φ)
    ((ShortComplex.homologyMap f).hom
      (((SingularChainComplex ℚ P.fst).sc n).moduleCatHomologyClass z)) = _
  rw [ShortComplex.moduleCatHomologyClass_naturality, i1_relativeCocycleClass_pairing]
  rfl

end HodgeLean.Foundations.BundleResolution
