import HodgeLean.Foundations.Program.G32Native.CompactNearestManifoldRegularity

/-! # One analytic Euclidean neighbourhood retraction near a compact carrier

Its domain is chosen inside the analytic locus of the common nearest-base map.
The map retains its identity on every embedded point of the compact carrier.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Function Set Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

/-- The compact nearest-base selection retracts an open ambient neighbourhood
of the carrier's interior analytically onto the original manifold.
The nearest selection itself is retained, so restrictions agree literally.
Source: `compactNearest_retraction_analyticAt` and Mathlib,
`contMDiffAt_iff_contMDiffAt_nhds`; Lee, Introduction to Smooth Manifolds,
second edition, Euclidean normal-neighbourhood construction.
HC no distance; AV milestone no distance. -/
theorem compactNearest_analytic_retraction
    {E M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ω M]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (C : Set M) [CompactSpace C] [Nonempty C]
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ω e)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x))
    (hemb : Topology.IsEmbedding (fun z : C => e z)) :
    let r : F → M := fun y => ((CompactNearest.nearest (fun z : C => e z)
      (he.continuous.comp continuous_subtype_val) y : C) : M)
    ∃ D : TopologicalSpace.Opens F,
      (e '' interior C ⊆ D) ∧
      ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ω r D ∧
      ∀ c : C, r (e c) = c := by
  let r : F → M := fun y => ((CompactNearest.nearest (fun z : C => e z)
    (he.continuous.comp continuous_subtype_val) y : C) : M)
  let S : Set F := {y | ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ω r y}
  let D : TopologicalSpace.Opens F := ⟨interior S, isOpen_interior⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    let cC : C := ⟨c, interior_subset hc⟩
    have ha : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ω r (e c) :=
      compactNearest_retraction_analyticAt C e he hi hemb cC hc
    exact mem_interior_iff_mem_nhds.mpr
      ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp ha)
  · intro y hy
    exact (interior_subset hy).contMDiffWithinAt
  · intro c
    exact congrArg Subtype.val (CompactNearest.nearest_fix (fun z : C => e z)
      (he.continuous.comp continuous_subtype_val) hemb.injective c)

#print axioms compactNearest_analytic_retraction

end HodgeLean.Foundations.TubularEuler
