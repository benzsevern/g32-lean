import HodgeLean.Foundations.Program.G32Native.CompactNearestRetraction
import Mathlib.Topology.Compactness.LocallyCompact

/-! # Euclidean retractions near a compact subset of an analytic embedding

A compact carrier is chosen inside the original manifold. The resulting
nearest-base map is one analytic ambient retraction near the specified set.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Function Set Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler

/-- An injective analytic immersion gives one analytic neighbourhood retraction
near any nonempty compact subset of the original manifold.
No normal bundle or pre-existing retraction is assumed.
Source: `compactNearest_analytic_retraction` and Mathlib,
`exists_compact_superset`; Lee, Introduction to Smooth Manifolds, second
edition, Euclidean normal-neighbourhood construction.
HC no distance; AV milestone no distance. -/
theorem analyticEmbedding_retraction_near_compact
    {E M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ω M] [T2Space M] [LocallyCompactSpace M]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ω e)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x)) (hinj : Injective e)
    (K : Set M) (hK : IsCompact K) (hKN : K.Nonempty) :
    ∃ (C : Set M), IsCompact C ∧ K ⊆ interior C ∧
      ∃ (D : TopologicalSpace.Opens F) (r : F → M),
        e '' K ⊆ D ∧ ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ω r D ∧
        ∀ c ∈ C, r (e c) = c := by
  obtain ⟨C, hC, hKC⟩ := exists_compact_superset hK
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  obtain ⟨x, hx⟩ := hKN
  letI : Nonempty C := ⟨⟨x, interior_subset (hKC hx)⟩⟩
  have hEmb : Topology.IsEmbedding (fun z : C => e z) :=
    ((he.continuous.comp continuous_subtype_val).isClosedEmbedding
      (fun u v huv => Subtype.ext (hinj huv))).isEmbedding
  let r : F → M := fun y => ((CompactNearest.nearest (fun z : C => e z)
    (he.continuous.comp continuous_subtype_val) y : C) : M)
  obtain ⟨D, hD, hreg, hfix⟩ := compactNearest_analytic_retraction C e he hi hEmb
  refine ⟨C, hC, hKC, D, r, ?_, hreg, ?_⟩
  · exact (Set.image_mono hKC).trans hD
  · intro c hc
    exact hfix ⟨c, hc⟩

#print axioms analyticEmbedding_retraction_near_compact

end HodgeLean.Foundations.TubularEuler
