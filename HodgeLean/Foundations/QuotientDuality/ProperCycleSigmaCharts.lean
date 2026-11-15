import HodgeLean.Foundations.QuotientDuality.ProperCycleCompactManifoldPointDetection

/-! # Charts on disjoint unions of actual smooth pieces
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open TopologicalSpace Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- Disjoint unions of actual charted pieces retain their charts by the original open summand inclusions.
Source: IsOpenEmbedding.sigmaMk; IsOpenEmbedding.toOpenPartialHomeomorph.
HC no distance; AV milestone no distance. -/
def properCycle_sigma_chartedSpace
    {ι : Type} (E : Type) [TopologicalSpace E]
    (Y : ι → Type) [∀ i, TopologicalSpace (Y i)] [∀ i, Nonempty (Y i)]
    [∀ i, ChartedSpace E (Y i)] :
    ChartedSpace E (Σ i, Y i) := by
  let F (i : ι) : OpenPartialHomeomorph (Y i) (Σ j, Y j) :=
    (IsOpenEmbedding.sigmaMk (i := i)).toOpenPartialHomeomorph (Sigma.mk i)
  refine
    { atlas := Set.univ
      chartAt := fun x => (F x.1).symm.trans (chartAt E x.2)
      mem_chart_source := ?_
      chart_mem_atlas := fun _ => Set.mem_univ _ }
  intro x
  have hx : x.2 ∈ (F x.1).source := by
    dsimp only [F]
    rw [IsOpenEmbedding.toOpenPartialHomeomorph_source]
    trivial
  have hFx : F x.1 x.2 = x := rfl
  change x ∈ (F x.1).target ∧ (F x.1).symm x ∈ (chartAt E x.2).source
  constructor
  · rw [← hFx]
    exact (F x.1).map_source hx
  · have hinv : (F x.1).symm x = x.2 :=
      (congrArg (F x.1).symm hFx.symm).trans ((F x.1).left_inv hx)
    rw [hinv]
    exact mem_chart_source E x.2

end HodgeLean.Foundations.QuotientDuality
