import HodgeLean.Foundations.RationalHomologyManifold.SupportedRelativePatching
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-! Open neighborhood witnesses for actual finite supported-chain equality.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Equality of finite relative chains supported on a set persists on an open neighborhood of that set.
Source: Bredon, Sheaf Theory, second edition, VI.12; compact simplex images in finite singular chains.
HC no distance; AV milestone no distance.
-/
theorem supportedChainProjection_eq_near_set (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (K : Set X) (z w : (SingularChainComplex ℚ X).X n)
    (h : (relativeChainProjection ℚ (TopPair.ofSubset (X := X) Kᶜ)).f n z =
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) Kᶜ)).f n w) :
    ∃ V : Opens X, K ⊆ V ∧
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n z =
        (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f n w := by
  classical
  let c := (chainGroupFinsuppIso ℚ X n).toLinearEquiv (z - w)
  let A : Set X := ⋃ s ∈ c.support, Set.range (X.toSSetObjEquiv _ s)
  have hAc : IsCompact A := c.support.isCompact_biUnion
    (fun s _ => isCompact_range (X.toSSetObjEquiv _ s).continuous)
  let V : Opens X := ⟨Aᶜ, hAc.isClosed.isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  · intro x hxK hxA
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hxA
    obtain ⟨hsC, u, hu⟩ := Set.mem_iUnion.mp hs
    have hc : c s ≠ 0 := Finsupp.mem_support_iff.mp hsC
    apply hc
    change (singularChainCoefficient X n s).hom (z - w) = 0
    have he := (supportedChainProjection_eq_iff_coefficients X K n z w).mp h s
      ⟨u, hu ▸ hxK⟩
    rw [map_sub, he, sub_self]
  · apply (supportedChainProjection_eq_iff_coefficients X (V : Set X) n z w).mpr
    rintro s ⟨u, hu⟩
    apply sub_eq_zero.mp
    rw [← map_sub]
    by_contra hc
    have hsC : s ∈ c.support := Finsupp.mem_support_iff.mpr hc
    apply hu
    exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hsC, u, rfl⟩⟩

#print axioms supportedChainProjection_eq_near_set
end HodgeLean.Foundations.RationalHomologyManifold
