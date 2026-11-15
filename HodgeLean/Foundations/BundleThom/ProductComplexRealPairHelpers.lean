import HodgeLean.Foundations.BundleThom.RealProductRelativeVanishingHelpers

/-! # Actual real coordinates for complex product pairs

HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Splitting complex normal coordinates into consecutive real coordinates retains the actual arbitrary-base product pair.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex normal coordinates. -/
def i1_productComplexRealPairIso (B : Type) [TopologicalSpace B] (k : ℕ) :
    i1_productNormalPair B k ≅ i1_realProductNormalPair B (k * 2) :=
  TopPair.isoOfSubset
    ((Homeomorph.refl B).prodCongr (complexRealHomeomorph k))
    (fun _ => not_congr (Complex.piCoordCLE k).map_eq_zero_iff)

/-- Actual complex product relative homology vanishes below twice the rank over every topological base.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6; Hatcher, §2.2, complex normal coordinates and relative products. -/
theorem i1_productNormalRelativeHomology_isZero_of_lt
    (B : Type) [TopologicalSpace B] (k n : ℕ) (hn : n < 2 * k) :
    CategoryTheory.Limits.IsZero (RelativeHomology ℚ (i1_productNormalPair B k) n) := by
  have h := i1_realProductNormalRelativeHomology_isZero_of_lt B (k * 2) n (by omega)
  exact h.of_iso ((relativeHomologyFunctor ℚ n).mapIso (i1_productComplexRealPairIso B k))

end HodgeLean.Foundations.BundleThom
