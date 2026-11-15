import HodgeLean.Foundations.BundleThom.ActualDomainBinaryCoclassGluingHelpers
import HodgeLean.Foundations.BundleThom.SubsetRelativeCoclassNaturalityHelpers

/-! # Binary gluing with actual topological domain restrictions -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Actual relative coclasses agreeing on the supplied intersection extend with both actual domain restrictions.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, relative Mayer–Vietoris. -/
theorem i1_actualRelativeBinaryCoclass_gluing (X : TopCat) (Z U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (u : RelativeCohomology ℚ (i1_subsetRelativePair X Z U) n)
    (v : RelativeCohomology ℚ (i1_subsetRelativePair X Z V) n)
    (huv : relativeCohomologyMap ℚ n
        (i1_subsetRelativePairMap X Z (Set.inter_subset_left : U ∩ V ⊆ U)) u =
      relativeCohomologyMap ℚ n
        (i1_subsetRelativePairMap X Z (Set.inter_subset_right : U ∩ V ⊆ V)) v) :
    ∃ z : RelativeCohomology ℚ (TopPair.ofSubset (X := X) Z) n,
      relativeCohomologyMap ℚ n (i1_subsetRelativePairInclusion X Z U) z = u ∧
      relativeCohomologyMap ℚ n (i1_subsetRelativePairInclusion X Z V) z = v := by
  have he := congrArg (i1_subsetRelativeCoclassEquiv X Z (U ∩ V) n) huv
  rw [i1_subsetRelativeCoclassEquiv_naturality,
    i1_subsetRelativeCoclassEquiv_naturality] at he
  apply i1_actualDomainBinaryCoclass_gluing X Z U V hU hV hcover n u v
  let F := i1_relativeSubcomplexChainFunctor (TopCat.toSSet.obj X) (i1_singularSubsetRange X Z)
  have ht : ∀ (A : (TopCat.toSSet.obj X).Subcomplex)
      (hAU : A ≤ i1_singularSubsetRange X U) (hAV : A ≤ i1_singularSubsetRange X V),
      A = i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V →
      i1_chainDualPullback n (F.map (homOfLE hAU)) (i1_subsetRelativeCoclassEquiv X Z U n u) =
        i1_chainDualPullback n (F.map (homOfLE hAV)) (i1_subsetRelativeCoclassEquiv X Z V n v) →
      i1_chainDualPullback n (F.map (homOfLE (inf_le_left :
        i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V ≤ i1_singularSubsetRange X U)))
        (i1_subsetRelativeCoclassEquiv X Z U n u) =
      i1_chainDualPullback n (F.map (homOfLE (inf_le_right :
        i1_singularSubsetRange X U ⊓ i1_singularSubsetRange X V ≤ i1_singularSubsetRange X V)))
        (i1_subsetRelativeCoclassEquiv X Z V n v) := by
    intro A hAU hAV hA hh
    subst A
    exact hh
  exact ht _ _ _ (i1_singularSubsetRange_inter X U V) he

end HodgeLean.Foundations.BundleThom
