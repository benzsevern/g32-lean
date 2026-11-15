import HodgeLean.Foundations.QuotientDuality.ProperCycleSigmaCharts

/-! # Actual ambient charts supplied by open charted pieces
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- Every point in an actual open embedding of a charted piece lies in an ambient chart with the same model.
Source: IsOpenEmbedding.toOpenPartialHomeomorph; OpenPartialHomeomorph.trans.
HC no distance; AV milestone no distance. -/
lemma properCycle_open_piece_chart
    {E : Type} [TopologicalSpace E] (X Y : TopCat.{0}) [ChartedSpace E Y]
    (f : Y ⟶ X) (hf : IsOpenEmbedding f) (y : Y) :
    ∃ e : OpenPartialHomeomorph X E, f y ∈ e.source := by
  letI : Nonempty Y := ⟨y⟩
  let H := hf.toOpenPartialHomeomorph f
  have hy : y ∈ H.source := by
    rw [IsOpenEmbedding.toOpenPartialHomeomorph_source]
    trivial
  refine ⟨H.symm.trans (chartAt E y), ?_⟩
  change f y ∈ H.target ∧ H.symm (f y) ∈ (chartAt E y).source
  have he : H y = f y := rfl
  constructor
  · exact he ▸ H.map_source hy
  · have hi : H.symm (f y) = y := (congrArg H.symm he.symm).trans (H.left_inv hy)
    rw [hi]
    exact mem_chart_source E y

end HodgeLean.Foundations.QuotientDuality
