import HodgeLean.Foundations.QuotientDuality.ProperCycleTopPairAmbientExt
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeDegreeTransport

/-! # Original relative-chain transports under actual subset equality
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Equality transport of actual subsets retains the literal identity ambient map on their topological pairs.
Source: CategoryTheory.eqToIso; AlgebraicTopology.Singular.TopPair.ofSubset.
HC no distance; AV milestone no distance. -/
theorem properCycle_subset_eq_pair_ambient (X : TopCat.{0}) (A B : Set X) (e : A = B) :
    TopPair.Hom.fst (eqToIso (congrArg (fun U : Set X => TopPair.ofSubset (X := X) U) e)).hom = 𝟙 X := by
  subst B
  rfl

/-- The original relative-chain equality transport is the actual relative functor image of the corresponding equality-induced pair isomorphism.
Source: CategoryTheory.eqToIso; AlgebraicTopology.Singular.relativeChainFunctor.
HC no distance; AV milestone no distance. -/
theorem properCycle_relative_chain_subset_eq (X : TopCat.{0}) (A B : Set X) (e : A = B) :
    eqToIso (congrArg (fun U : Set X => (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) U)) e) =
      (relativeChainFunctor ℚ).mapIso
        (eqToIso (congrArg (fun U : Set X => TopPair.ofSubset (X := X) U) e)) := by
  subst B
  apply Iso.ext
  change 𝟙 ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) A)) =
    (relativeChainFunctor ℚ).map (𝟙 (TopPair.ofSubset (X := X) A))
  rw [CategoryTheory.Functor.map_id]

end HodgeLean.Foundations.QuotientDuality
