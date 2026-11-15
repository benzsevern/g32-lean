import HodgeLean.Foundations.QuotientDuality.ProperCycleIsolatedComponentSupport

/-! # Open component pieces inside actual collected supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- An open piece of an embedded space is open in the target when the embedded range is a neighborhood at every point of that piece.
Source: IsInducing.map_nhds_of_mem; IsOpenEmbedding.map_nhds_eq.
HC no distance; AV milestone no distance. -/
lemma properCycle_embedding_open_composite
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : Y → Z) (g : X → Y) (hf : IsEmbedding f) (hg : IsOpenEmbedding g)
    (hnb : ∀ x, Set.range f ∈ 𝓝 (f (g x))) : IsOpenEmbedding (f ∘ g) := by
  refine ⟨hf.comp hg.isEmbedding, isOpen_iff_mem_nhds.mpr ?_⟩
  rintro z ⟨x, rfl⟩
  have he : Filter.map (f ∘ g) (𝓝 x) = 𝓝 (f (g x)) := by
    rw [← Filter.map_map, hg.map_nhds_eq,
      hf.isInducing.map_nhds_of_mem (g x) (hnb x)]
  change Set.range (f ∘ g) ∈ 𝓝 (f (g x))
  rw [← he]
  exact Filter.mem_map.mpr (Filter.mem_of_superset Filter.univ_mem (fun y _ => ⟨y, rfl⟩))

end HodgeLean.Foundations.QuotientDuality
