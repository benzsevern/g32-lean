import HodgeLean.Foundations.BundleThom.Defs

/-! # Actual real product normal pairs

The real normal coordinate is retained for the two-cap homology induction.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- The actual product pair relative to the complement of the real zero-normal plane.
Source: Hatcher, Algebraic Topology, §2.1 and §2.2, relative Euclidean product pairs. -/
def i1_realProductNormalPair (B : Type) [TopologicalSpace B] (d : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (B × (Fin d → ℝ))) {p | p.2 ≠ 0}

end HodgeLean.Foundations.BundleThom
