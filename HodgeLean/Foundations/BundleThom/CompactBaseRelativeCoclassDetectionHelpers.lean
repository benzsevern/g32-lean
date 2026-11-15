import HodgeLean.Foundations.BundleThom.CompactBaseSingularDomainHelpers
import HodgeLean.Foundations.BundleThom.ActualDirectedRelativeCoclassDetectionHelpers
import HodgeLean.Foundations.BundleThom.SubsetRelativeComparisonHelpers

/-! # Rational relative coclass detection over compact parts of a continuous base

Compact inverse-image domains detect the actual relative classes in every degree.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular Simplicial
namespace HodgeLean.Foundations.BundleThom

/-- Actual relative restrictions over every compact subset of a continuous base detect rational relative coclasses.
Source: Hatcher, Algebraic Topology, §2.1 and §3.1, finite support of singular chains and universal coefficients. -/
theorem i1_relativeCoclass_ext_of_compactBase_restrictions {B : Type} [TopologicalSpace B]
    (X : TopCat) (Z : Set X) (f : X → B) (hf : Continuous f) (n : ℕ)
    (u v : RelativeCohomology ℚ (TopPair.ofSubset (X := X) Z) n)
    (h : ∀ K : Compacts B, relativeCohomologyMap ℚ n
        (i1_subsetRelativePairInclusion X Z (f ⁻¹' (K : Set B))) u =
      relativeCohomologyMap ℚ n
        (i1_subsetRelativePairInclusion X Z (f ⁻¹' (K : Set B))) v) : u = v := by
  apply i1_actualDirectedRelativeCoclass_ext X Z (i1_compactBaseSingularDomain X f)
    (i1_compactBaseSingularDomain_monotone X f).directed_le n
    (i1_compactBaseSingularDomain_cover X f hf (Opposite.op ⦋n⦌))
  intro K
  have he := congrArg (i1_subsetRelativeCoclassEquiv X Z (f ⁻¹' (K : Set B)) n) (h K)
  rw [i1_subsetRelativeCoclassEquiv_restriction,
    i1_subsetRelativeCoclassEquiv_restriction] at he
  exact he

end HodgeLean.Foundations.BundleThom
