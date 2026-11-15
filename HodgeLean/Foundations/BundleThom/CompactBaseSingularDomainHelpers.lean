import HodgeLean.Foundations.BundleThom.SingularSubsetIntersectionHelpers
import Mathlib.Topology.Sets.Compacts

/-! # Actual singular domains over compact base subsets

The domain is the full inverse image of the supplied compact subset of the base.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology AlgebraicTopology.Singular Simplicial
namespace HodgeLean.Foundations.BundleThom

/-- The actual singular domain lying over a supplied compact base subset.
Source: Hatcher, Algebraic Topology, §2.1, compact images of singular simplices. -/
def i1_compactBaseSingularDomain {B : Type} [TopologicalSpace B]
    (X : TopCat) (f : X → B) (K : Compacts B) : (TopCat.toSSet.obj X).Subcomplex :=
  i1_singularSubsetRange X (f ⁻¹' (K : Set B))

/-- Compact base-subset inclusion induces inclusion of the actual singular domains.
Source: Hatcher, Algebraic Topology, §2.1, singular simplices in nested subspaces. -/
theorem i1_compactBaseSingularDomain_monotone {B : Type} [TopologicalSpace B]
    (X : TopCat) (f : X → B) : Monotone (i1_compactBaseSingularDomain X f) := by
  intro K L hKL n σ hσ
  change σ ∈ (i1_singularSubsetRange X (f ⁻¹' (L : Set B))).obj n
  apply (i1_mem_singularSubsetRange_iff X _ σ).mpr
  intro t
  exact hKL ((i1_mem_singularSubsetRange_iff X (f ⁻¹' (K : Set B)) σ).mp hσ t)

/-- Every actual singular simplex lies over some compact subset of the supplied continuous base.
Source: Hatcher, Algebraic Topology, §2.1, compactness of the standard simplex. -/
theorem i1_compactBaseSingularDomain_cover {B : Type} [TopologicalSpace B]
    (X : TopCat) (f : X → B) (hf : Continuous f) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    ∃ K : Compacts B, σ ∈ (i1_compactBaseSingularDomain X f K).obj n := by
  let g := f ∘ X.toSSetObjEquiv n σ
  let K : Compacts B := ⟨Set.range g, isCompact_range (hf.comp (X.toSSetObjEquiv n σ).continuous)⟩
  refine ⟨K, (i1_mem_singularSubsetRange_iff X _ σ).mpr ?_⟩
  intro t
  exact ⟨t, rfl⟩

end HodgeLean.Foundations.BundleThom
