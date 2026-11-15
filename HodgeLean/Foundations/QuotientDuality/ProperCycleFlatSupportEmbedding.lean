import HodgeLean.Foundations.QuotientDuality.ProperCycleFlatSupportChart

/-! # Actual tangential open embeddings of flattened support charts
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- Projection of the original flattened support chart is an actual open embedding into its tangential model.
Source: properCycle_flat_support_chart_homeomorph; IsOpen.isOpenEmbedding_subtypeVal.
HC no distance; AV milestone no distance. -/
lemma properCycle_flat_support_chart_isOpenEmbedding
    (X : TopCat.{0}) (S : Set X) {E Y : Type} [TopologicalSpace E] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (y : Y)
    (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y) :
    IsOpenEmbedding (fun s : {s : S | s.val ∈ e.source} => (e s.val.val).1) := by
  let H := properCycle_flat_support_chart_homeomorph X S e y hflat
  have ho : IsOpen {v : E | (v, y) ∈ e.target} :=
    e.open_target.preimage (continuous_id.prodMk continuous_const)
  exact ho.isOpenEmbedding_subtypeVal.comp H.isOpenEmbedding

end HodgeLean.Foundations.QuotientDuality
