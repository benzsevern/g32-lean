import HodgeLean.Foundations.BundleThom.SubsetRelativeComparisonHelpers

/-! # Binary gluing with actual topological domain restrictions -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Compatible actual domain coclasses extend with both supplied topological restrictions.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, relative Mayer–Vietoris. -/
theorem i1_actualDomainBinaryCoclass_gluing (X : TopCat) (Z U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (u : RelativeCohomology ℚ (i1_subsetRelativePair X Z U) n)
    (v : RelativeCohomology ℚ (i1_subsetRelativePair X Z V) n)
    (huv : i1_chainDualPullback n ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X)
        (i1_singularSubsetRange X Z)).map (homOfLE (inf_le_left :
          i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V ≤ i1_singularSubsetRange X U))) (i1_subsetRelativeCoclassEquiv X Z U n u) =
      i1_chainDualPullback n ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X)
        (i1_singularSubsetRange X Z)).map (homOfLE (inf_le_right :
          i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V ≤ i1_singularSubsetRange X V))) (i1_subsetRelativeCoclassEquiv X Z V n v)) :
    ∃ z : RelativeCohomology ℚ (TopPair.ofSubset (X := X) Z) n,
      relativeCohomologyMap ℚ n (i1_subsetRelativePairInclusion X Z U) z = u ∧
      relativeCohomologyMap ℚ n (i1_subsetRelativePairInclusion X Z V) z = v := by
  obtain ⟨z, hzU, hzV⟩ := i1_topologicalBinaryCoclass_gluing X Z U V hU hV hcover n
    (i1_subsetRelativeCoclassEquiv X Z U n u) (i1_subsetRelativeCoclassEquiv X Z V n v) huv
  refine ⟨z, ?_, ?_⟩
  · apply (i1_subsetRelativeCoclassEquiv X Z U n).injective
    rw [i1_subsetRelativeCoclassEquiv_restriction]
    exact hzU
  · apply (i1_subsetRelativeCoclassEquiv X Z V n).injective
    rw [i1_subsetRelativeCoclassEquiv_restriction]
    exact hzV

end HodgeLean.Foundations.BundleThom
