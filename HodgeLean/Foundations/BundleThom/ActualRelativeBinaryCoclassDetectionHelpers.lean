import HodgeLean.Foundations.BundleThom.ActualRelativeBinaryCoclassGluingHelpers
import HodgeLean.Foundations.BundleThom.BinaryChainCoclassDetectionHelpers

/-! # Actual binary relative coclass detection -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Lower intersection homology vanishing makes the two actual open-domain restrictions determine a relative coclass.
Source: Hatcher, Algebraic Topology, §3.1, relative Mayer–Vietoris uniqueness. -/
theorem i1_actualRelativeBinaryCoclass_ext (X : TopCat) (Z U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (hzero : IsZero (((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X)
      (i1_singularSubsetRange X Z)).obj
      (i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V)).homology n))
    (u v : RelativeCohomology ℚ (TopPair.ofSubset (X := X) Z) (n + 1))
    (hu : relativeCohomologyMap ℚ (n + 1) (i1_subsetRelativePairInclusion X Z U) u =
      relativeCohomologyMap ℚ (n + 1) (i1_subsetRelativePairInclusion X Z U) v)
    (hv : relativeCohomologyMap ℚ (n + 1) (i1_subsetRelativePairInclusion X Z V) u =
      relativeCohomologyMap ℚ (n + 1) (i1_subsetRelativePairInclusion X Z V) v) : u = v := by
  let F := i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)
  let e := i1_binaryRelativeSmallCoclassEquiv X Z U V hU hV hcover (n + 1)
  have hu' := congrArg (i1_subsetRelativeCoclassEquiv X Z U (n + 1)) hu
  have hv' := congrArg (i1_subsetRelativeCoclassEquiv X Z V (n + 1)) hv
  rw [i1_subsetRelativeCoclassEquiv_restriction, i1_subsetRelativeCoclassEquiv_restriction] at hu' hv'
  have hrestriction (W : (TopCat.toSSet.obj X).Subcomplex)
      (hW : W ≤ i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V)
      (c : RelativeCohomology ℚ (TopPair.ofSubset (X := X) Z) (n + 1)) :
      i1_chainDualPullback (n + 1) (F.map (homOfLE hW)) (e c) =
        i1_chainDualPullback (n + 1) (i1_relativeSmallChainComparison X Z W) c := by
    change i1_chainDualPullback (n + 1) (F.map (homOfLE hW))
      (i1_chainDualPullback (n + 1) (i1_relativeSmallChainComparison X Z
        (i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V)) c) = _
    rw [← LinearMap.comp_apply, ← i1_chainDualPullback_comp,
      i1_relativeSmallChainComparison_naturality]
  haveI := i1_relativeSubcomplexChainMap_mono (TopCat.toSSet.obj X)
    (i1_singularSubsetRange X Z) (i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V)
    (i1_singularSubsetRange X U) inf_le_left
  apply e.injective
  apply i1_binaryChainCoclass_ext
    (i1_relativeSubcomplexChains_isPushout (TopCat.toSSet.obj X)
      (i1_singularSubsetRange X Z) (i1_singularSubsetRange X U) (i1_singularSubsetRange X V)) n hzero
  · rw [hrestriction, hrestriction]
    exact hu'
  · rw [hrestriction, hrestriction]
    exact hv'

end HodgeLean.Foundations.BundleThom
