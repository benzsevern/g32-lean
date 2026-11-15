import HodgeLean.Foundations.QuotientDuality.ProperCycleSigmaCharts

/-! # Open embeddings of disjoint actual component pieces
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- A jointly injective family of open embeddings defines an open embedding of its actual disjoint union.
Source: continuous_sigma; isOpenMap_sigma; IsOpenEmbedding.of_continuous_injective_isOpenMap.
HC no distance; AV milestone no distance. -/
lemma properCycle_sigma_open_embedding
    {ι : Type} (Y : ι → Type) [∀ i, TopologicalSpace (Y i)]
    {Z : Type} [TopologicalSpace Z] (f : ∀ i, Y i → Z)
    (hf : ∀ i, IsOpenEmbedding (f i))
    (hinj : Function.Injective (fun y : Σ i, Y i => f y.1 y.2)) :
    IsOpenEmbedding (fun y : Σ i, Y i => f y.1 y.2) :=
  .of_continuous_injective_isOpenMap (continuous_sigma (fun i => (hf i).continuous))
    hinj (isOpenMap_sigma.mpr (fun i => (hf i).isOpenMap))

end HodgeLean.Foundations.QuotientDuality
