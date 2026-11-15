import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportedCapProjection
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Actual homology lifts from the literal relative projection -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- A global homology class with zero literal relative projection comes from the original subspace homology.
Source: Hatcher, Algebraic Topology, section 2.1, exact homology sequence of a pair.
HC no distance; AV milestone no distance. -/
lemma properCycle_homology_lift_of_relative_projection_zero
    (X : TopCat.{0}) (B : Set X) (n : ℕ) (c : Homology ℚ X n)
    (hc : (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) B) n).hom c = 0) :
    ∃ b : Homology ℚ (TopCat.of B) n,
      homologyMap ℚ n (TopPair.ofSubset (X := X) B).map b = c := by
  let P := TopPair.ofSubset (X := X) B
  let f := ((chainPairFunctor ℚ).obj P).hom
  letI : Mono f := relativeChainMap_mono ℚ P
  let S : ShortComplex (ChainCategory ℚ) :=
    ShortComplex.mk f (relativeChainProjection ℚ P) (subspaceChainMap_relativeChainProjection ℚ P)
  letI : Epi S.g := by
    change Epi (CategoryTheory.Limits.cokernel.π f)
    infer_instance
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  have hex := hS.homology_exact₂ n
  have hfg := hex.moduleCat_range_eq_ker
  change LinearMap.range (homologyMap ℚ n P.map) =
    LinearMap.ker (relativeHomologyProjection ℚ P n).hom at hfg
  have hc' : c ∈ LinearMap.range (homologyMap ℚ n P.map) := by
    rw [hfg]
    exact hc
  exact hc'

end HodgeLean.Foundations.QuotientDuality
