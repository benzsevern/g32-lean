import HodgeLean.Foundations.BundleThom.BinaryRelativeSmallCoclassHelpers
import HodgeLean.Foundations.BundleThom.BinaryRelativeCoclassGluingHelpers

/-! # Gluing to an actual topological relative coclass over a binary open cover

The two input small-domain classes retain their actual intersection maps, and the output lies in the supplied topological pair.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Compatible coclasses on the two actual singular range domains of a binary open cover extend to the supplied topological relative pair.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, relative Mayer–Vietoris coclass gluing. -/
theorem i1_topologicalBinaryCoclass_gluing (X : TopCat) (Z U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (u : ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)).obj
      (i1_singularSubsetRange X U)).linearDualCochainComplex.homology n)
    (v : ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)).obj
      (i1_singularSubsetRange X V)).linearDualCochainComplex.homology n)
    (huv : i1_chainDualPullback n ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X)
        (i1_singularSubsetRange X Z)).map (homOfLE (inf_le_left :
          i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V ≤ i1_singularSubsetRange X U))) u =
      i1_chainDualPullback n ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X)
        (i1_singularSubsetRange X Z)).map (homOfLE (inf_le_right :
          i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V ≤ i1_singularSubsetRange X V))) v) :
    ∃ z : RelativeCohomology ℚ (TopPair.ofSubset (X := X) Z) n,
      i1_chainDualPullback n (i1_relativeSmallChainComparison X Z (i1_singularSubsetRange X U)) z = u ∧
      i1_chainDualPullback n (i1_relativeSmallChainComparison X Z (i1_singularSubsetRange X V)) z = v := by
  obtain ⟨w, hwU, hwV⟩ := i1_binaryRelativeSubcomplexCoclass_gluing
    (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)
    (i1_singularSubsetRange X U) (i1_singularSubsetRange X V) n u v huv
  let e := i1_binaryRelativeSmallCoclassEquiv X Z U V hU hV hcover n
  let z := e.symm w
  have hz : i1_chainDualPullback n (i1_relativeSmallChainComparison X Z
      (i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V)) z = w :=
    e.apply_symm_apply w
  refine ⟨z, ?_, ?_⟩
  · rw [← i1_relativeSmallChainComparison_naturality X Z (i1_singularSubsetRange X U)
      (i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V) le_sup_left,
      i1_chainDualPullback_comp, LinearMap.comp_apply, hz]
    exact hwU
  · rw [← i1_relativeSmallChainComparison_naturality X Z (i1_singularSubsetRange X V)
      (i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V) le_sup_right,
      i1_chainDualPullback_comp, LinearMap.comp_apply, hz]
    exact hwV

end HodgeLean.Foundations.BundleThom
