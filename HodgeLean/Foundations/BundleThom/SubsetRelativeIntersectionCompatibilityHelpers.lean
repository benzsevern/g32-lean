import HodgeLean.Foundations.BundleThom.SubsetRelativeCoclassNaturalityHelpers

/-! # Actual intersection compatibility in singular-range relative coordinates

The supplied relative coclasses and both actual intersection restrictions remain in the comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Equality on an actual relative-domain intersection gives equality of the two actual singular-range relative pullbacks.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, naturality of relative domain coordinates. -/
theorem i1_subsetRelativeCoclassEquiv_intersection_compatible (X : TopCat) (Z U V : Set X)
    (n : ℕ) (u : RelativeCohomology ℚ (i1_subsetRelativePair X Z U) n)
    (v : RelativeCohomology ℚ (i1_subsetRelativePair X Z V) n)
    (huv : relativeCohomologyMap ℚ n
        (i1_subsetRelativePairMap X Z (Set.inter_subset_left : U ∩ V ⊆ U)) u =
      relativeCohomologyMap ℚ n
        (i1_subsetRelativePairMap X Z (Set.inter_subset_right : U ∩ V ⊆ V)) v) :
    i1_chainDualPullback n ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X)
        (i1_singularSubsetRange X Z)).map (homOfLE (inf_le_left :
          i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V ≤ i1_singularSubsetRange X U)))
        (i1_subsetRelativeCoclassEquiv X Z U n u) =
      i1_chainDualPullback n ((i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X)
        (i1_singularSubsetRange X Z)).map (homOfLE (inf_le_right :
          i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V ≤ i1_singularSubsetRange X V)))
        (i1_subsetRelativeCoclassEquiv X Z V n v) := by
  have he := congrArg (i1_subsetRelativeCoclassEquiv X Z (U ∩ V) n) huv
  rw [i1_subsetRelativeCoclassEquiv_naturality, i1_subsetRelativeCoclassEquiv_naturality] at he
  let F := i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)
  have transfer (A : (TopCat.toSSet.obj X).Subcomplex)
      (hAU : A ≤ i1_singularSubsetRange X U) (hAV : A ≤ i1_singularSubsetRange X V)
      (hA : A = i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V)
      (h : i1_chainDualPullback n (F.map (homOfLE hAU)) (i1_subsetRelativeCoclassEquiv X Z U n u) =
        i1_chainDualPullback n (F.map (homOfLE hAV)) (i1_subsetRelativeCoclassEquiv X Z V n v)) :
      i1_chainDualPullback n (F.map (homOfLE (inf_le_left :
        i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V ≤ i1_singularSubsetRange X U)))
        (i1_subsetRelativeCoclassEquiv X Z U n u) =
      i1_chainDualPullback n (F.map (homOfLE (inf_le_right :
        i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V ≤ i1_singularSubsetRange X V)))
        (i1_subsetRelativeCoclassEquiv X Z V n v) := by
    subst A
    exact h
  exact transfer _ _ _ (i1_singularSubsetRange_inter X U V) he

end HodgeLean.Foundations.BundleThom
