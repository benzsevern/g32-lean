import HodgeLean.Foundations.BundleThom.SubsetRelativeChainIsoHelpers

/-! # Homology vanishing in actual relative-domain range coordinates

The equivalence retains the actual subset domain and its relative singular chain quotient.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Actual relative-domain homology vanishes exactly when homology in its actual singular-range coordinates vanishes.
Source: Hatcher, Algebraic Topology, §2.2, actual subspace chain coordinates. -/
theorem i1_subsetRelativeHomology_isZero_iff_range (X : TopCat) (Z U : Set X) (n : ℕ) :
    IsZero (RelativeHomology ℚ (i1_subsetRelativePair X Z U) n) ↔
      IsZero (((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X)
        (i1_singularSubsetRange X Z)).obj (i1_singularSubsetRange X U)).homology n) :=
  Iso.isZero_iff ((HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso
    (i1_subsetRelativeChainIso X Z U))

end HodgeLean.Foundations.BundleThom
