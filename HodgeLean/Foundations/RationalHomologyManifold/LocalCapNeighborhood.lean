import HodgeLean.Foundations.RationalHomologyManifold.PrismCapStabilization
import HodgeLean.RealDefs.Port.AlgebraicTopology.Singular.Sheaf.ChainStalk
import Mathlib.Topology.Separation.Regular

/-! Actual subdivided cap vanishes uniformly on a neighborhood of each local zero-cochain germ.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open scoped Topology
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Around a zero-cochain germ, cap of sufficiently subdivided chains vanishes uniformly on a smaller open neighborhood.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3; regular neighborhoods and subordinate subdivision prisms.
HC no distance; AV milestone no distance.
-/
theorem local_cap_subdivision_eventually_zero (X : TopCat.{0}) [RegularSpace X]
    (x : X) (U : Opens X) (hx : x ∈ U) (p q : ℕ)
    (φ : Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : cochainMap ℚ (TopCat.toSSet.map (TopPair.ofSubset (X := X) (U : Set X)).map) p φ = 0)
    (z : (SingularChainComplex ℚ X).X (p + q)) :
    ∃ (V : Opens X), x ∈ V ∧ V ≤ U ∧ ∃ m : ℕ, ∀ r : ℕ,
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f q
        (cap ℚ p q φ ((rationalSubdivisionIterate X (m + r)).f (p + q) z)) = 0 := by
  obtain ⟨K, hKnhds, hKclosed, hKU⟩ := exists_mem_nhds_isClosed_subset (U.isOpen.mem_nhds hx)
  have hcover : (U : Set X) ∪ Kᶜ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases hy : y ∈ K
    · exact Or.inl (hKU hy)
    · exact Or.inr hy
  obtain ⟨m, hm⟩ := relative_cap_subdivision_eventually_zero X U Kᶜ U.isOpen hKclosed.isOpen_compl
    hcover p q φ hφ z
  let V : Opens X := ⟨interior K, isOpen_interior⟩
  have hVK : (V : Set X) ⊆ K := interior_subset
  refine ⟨V, mem_interior_iff_mem_nhds.mpr hKnhds, hVK.trans hKU, m, fun r => ?_⟩
  let f := (relativeChainFunctor ℚ).map (supportInclusionPairMap X hVK)
  have hp := congrArg (fun a => a.f q) (relativeChainProjection_supportInclusion ℚ X hVK)
  change (relativeChainProjection ℚ (TopPair.ofSubset (X := X) Kᶜ)).f q ≫ f.f q =
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ)).f q at hp
  have h := congrArg (f.f q) (hm r)
  simp only [← ConcreteCategory.comp_apply, hp, map_zero] at h
  exact h

#print axioms local_cap_subdivision_eventually_zero
end HodgeLean.Foundations.RationalHomologyManifold
