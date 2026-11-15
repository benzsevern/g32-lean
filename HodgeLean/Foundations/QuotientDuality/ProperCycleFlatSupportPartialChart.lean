import HodgeLean.Foundations.QuotientDuality.ProperCycleEmbeddedFlatChart

/-! # Actual partial charts on literal flattened support
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- The original flattened support carries an actual partial chart with precisely the original tangential coordinate and the literal support intersection as source.
Source: properCycle_embedded_flat_chart, applied to the actual identity support embedding.
HC no distance; AV milestone no distance. -/
lemma properCycle_flat_support_partial_chart
    (X : TopCat.{0}) (S : Set X) {E Y : Type} [TopologicalSpace E] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (y0 : Y)
    (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y0)
    (z : S) (hz : z.val ∈ e.source) :
    ∃ c : OpenPartialHomeomorph (TopCat.of S) E,
      c.source = {s : S | s.val ∈ e.source} ∧
      ∀ s ∈ c.source, c s = (e s.val).1 := by
  let O : Opens (TopCat.of S) := ⟨{s : S | s.val ∈ e.source},
    e.open_source.preimage continuous_subtype_val⟩
  obtain ⟨c, hsrc, hval⟩ := properCycle_embedded_flat_chart X (TopCat.of S) S e y0 hflat
    (𝟙 (TopCat.of S)) IsEmbedding.id O (fun s _ => ⟨s, rfl⟩) (fun _ h => h) z hz
  exact ⟨c, hsrc, hval⟩

end HodgeLean.Foundations.QuotientDuality
