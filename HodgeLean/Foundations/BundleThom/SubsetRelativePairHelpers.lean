import HodgeLean.Foundations.BundleThom.TopologicalBinaryCoclassGluingHelpers

/-! # Actual relative pairs on supplied topological domains

The domain pair retains the ambient subspace and the exact intersection with the supplied relative subspace.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- The actual relative pair on a supplied domain, with the inherited relative subspace.
Source: Hatcher, Algebraic Topology, §2.1, relative subspace pairs. -/
def i1_subsetRelativePair (X : TopCat) (Z U : Set X) : TopPair :=
  TopPair.ofSubset (X := TopCat.of U) {u : U | u.1 ∈ Z}

/-- The actual domain inclusion is a map into the supplied ambient relative pair.
Source: Hatcher, Algebraic Topology, §2.1, maps of relative subspace pairs. -/
def i1_subsetRelativePairInclusion (X : TopCat) (Z U : Set X) :
    i1_subsetRelativePair X Z U ⟶ TopPair.ofSubset (X := X) Z :=
  TopPair.ofSubsetHom (topologicalSubsetInclusion X U) (fun _ h => h)

end HodgeLean.Foundations.BundleThom
