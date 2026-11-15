import HodgeLean.Foundations.BundleThom.RelativeSmallChainComparisonHelpers
import HodgeLean.Foundations.BundleThom.ChainDualQuasiIsoHelpers

/-! # Actual relative coclass transfer for supplied binary open covers

The equivalence is induced by the specified small-chain comparison into the actual topological relative pair.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Actual rational relative coclasses are equivalent to small relative coclasses for a supplied binary open cover.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, relative small chains and rational cohomology. -/
def i1_binaryRelativeSmallCoclassEquiv (X : TopCat) (Z U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    RelativeCohomology ℚ (TopPair.ofSubset (X := X) Z) n ≃ₗ[ℚ]
      ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)).obj
        (i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V)).linearDualCochainComplex.homology n := by
  letI := i1_binaryRelativeSmallChainComparison_quasiIso X Z U V hU hV hcover
  exact i1_chainDualPullbackEquiv n (i1_relativeSmallChainComparison X Z
    (i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V))

/-- The actual binary small coclass equivalence is exactly pullback by the specified relative chain comparison.
Source: Hatcher, Algebraic Topology, §3.1, rational small-chain transfer. -/
theorem i1_binaryRelativeSmallCoclassEquiv_apply (X : TopCat) (Z U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (u : RelativeCohomology ℚ (TopPair.ofSubset (X := X) Z) n) :
    i1_binaryRelativeSmallCoclassEquiv X Z U V hU hV hcover n u =
      i1_chainDualPullback n (i1_relativeSmallChainComparison X Z
        (i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V)) u := rfl

end HodgeLean.Foundations.BundleThom
