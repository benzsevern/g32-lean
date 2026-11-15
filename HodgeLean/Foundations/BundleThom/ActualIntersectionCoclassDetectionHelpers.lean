import HodgeLean.Foundations.BundleThom.ActualRelativeBinaryCoclassDetectionHelpers

/-! # Actual intersection homology in binary coclass detection -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Vanishing on the actual relative intersection pair makes the two actual domain restrictions determine a coclass.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, relative Mayer–Vietoris uniqueness. -/
theorem i1_actualIntersectionBinaryCoclass_ext (X : TopCat) (Z U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (hzero : IsZero (((relativeChainFunctor ℚ).obj (i1_subsetRelativePair X Z (U ∩ V))).homology n))
    (u v : RelativeCohomology ℚ (TopPair.ofSubset (X := X) Z) (n + 1))
    (hu : relativeCohomologyMap ℚ (n + 1) (i1_subsetRelativePairInclusion X Z U) u =
      relativeCohomologyMap ℚ (n + 1) (i1_subsetRelativePairInclusion X Z U) v)
    (hv : relativeCohomologyMap ℚ (n + 1) (i1_subsetRelativePairInclusion X Z V) u =
      relativeCohomologyMap ℚ (n + 1) (i1_subsetRelativePairInclusion X Z V) v) : u = v := by
  have hz := hzero.of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso
      (i1_subsetRelativeChainIso X Z (U ∩ V))).symm
  apply i1_actualRelativeBinaryCoclass_ext X Z U V hU hV hcover n _ u v hu hv
  rw [← i1_singularSubsetRange_inter]
  exact hz

end HodgeLean.Foundations.BundleThom
