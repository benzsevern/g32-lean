import HodgeLean.Foundations.BundleThom.ActualIntersectionCoclassDetectionHelpers

/-! # Relative homology vanishing over actual binary open covers

Rational duality transfers detection of coclasses back to vanishing of relative homology.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Rational relative homology vanishes exactly when the rational relative coclass space is a subsingleton.
Source: Hatcher, Algebraic Topology, §3.1, universal coefficients over a field. -/
theorem i1_relativeHomology_isZero_iff_cohomology_subsingleton (X : TopPair) (n : ℕ) :
    IsZero (RelativeHomology ℚ X n) ↔ Subsingleton (RelativeCohomology ℚ X n) := by
  let e := relativeCohomologyEquivDualHomology ℚ X n
  constructor
  · intro hz
    letI := ModuleCat.subsingleton_of_isZero hz
    exact e.injective.subsingleton
  · intro hc
    letI := hc
    haveI : Subsingleton (Module.Dual ℚ (RelativeHomology ℚ X n)) :=
      e.symm.injective.subsingleton
    haveI : Subsingleton (RelativeHomology ℚ X n) :=
      (Module.subsingleton_dual_iff ℚ).mp inferInstance
    exact ModuleCat.isZero_of_subsingleton _

/-- Vanishing on both actual domains and on the preceding-degree actual intersection forces relative homology to vanish on their binary union.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, relative Mayer–Vietoris and rational duality. -/
theorem i1_actualRelativeBinaryHomology_isZero (X : TopCat) (Z U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (hu : IsZero (RelativeHomology ℚ (i1_subsetRelativePair X Z U) (n + 1)))
    (hv : IsZero (RelativeHomology ℚ (i1_subsetRelativePair X Z V) (n + 1)))
    (hi : IsZero (RelativeHomology ℚ (i1_subsetRelativePair X Z (U ∩ V)) n)) :
    IsZero (RelativeHomology ℚ (TopPair.ofSubset (X := X) Z) (n + 1)) := by
  apply (i1_relativeHomology_isZero_iff_cohomology_subsingleton _ _).mpr
  haveI := (i1_relativeHomology_isZero_iff_cohomology_subsingleton _ _).mp hu
  haveI := (i1_relativeHomology_isZero_iff_cohomology_subsingleton _ _).mp hv
  constructor
  intro a b
  exact i1_actualIntersectionBinaryCoclass_ext X Z U V hU hV hcover n hi a b
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)

end HodgeLean.Foundations.BundleThom
