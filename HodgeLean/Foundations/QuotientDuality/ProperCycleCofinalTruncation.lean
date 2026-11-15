import HodgeLean.Foundations.QuotientDuality.ProperCycleMarkedChartModel

/-! # Actual polynomial truncations inside every specified neighborhood -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology TopologicalSpace HodgeLean.Foundations.ComplexTopology
namespace HodgeLean.Foundations.QuotientDuality

/-- Positive closed coordinate balls can be chosen inside every original open neighborhood.
Source: Munkres, Topology, sections 18 and 20, embeddings and metric neighborhoods.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_closed_ball_inside {X : Type} [TopologicalSpace X]
    (c : Marked.Chart X) (x : c.domain) (P : Opens X) (hxP : x.val ∈ P) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : c.domain,
      complexEuclideanCoordinates c.n (c.coordinates z).val ∈
        Metric.closedBall (complexEuclideanCoordinates c.n (c.coordinates x).val) R → z.val ∈ P := by
  let f : c.domain → EuclideanSpace ℝ (Fin (c.n + c.n)) :=
    fun z => complexEuclideanCoordinates c.n (c.coordinates z).val
  have hf : Topology.IsEmbedding f :=
    (complexEuclideanCoordinates c.n).isEmbedding.comp
      (Topology.IsEmbedding.subtypeVal.comp c.coordinates.isEmbedding)
  have hp : IsOpen (Subtype.val ⁻¹' (P : Set X) : Set c.domain) :=
    P.isOpen.preimage continuous_subtype_val
  obtain ⟨Q, hQ, heq⟩ := hf.isInducing.isOpen_iff.mp hp
  have hxQ : f x ∈ Q := by
    change x ∈ f ⁻¹' Q
    rw [heq]
    exact hxP
  obtain ⟨ε, hε, hεQ⟩ := Metric.isOpen_iff.mp hQ (f x) hxQ
  refine ⟨ε / 2, by positivity, ?_⟩
  intro z hz
  have hzQ : f z ∈ Q := hεQ (by
    change dist (f z) (f x) < ε
    exact (show dist (f z) (f x) ≤ ε / 2 from hz).trans_lt (by linarith))
  change z ∈ (Subtype.val ⁻¹' (P : Set X) : Set c.domain)
  rw [← heq]
  exact hzQ

end HodgeLean.Foundations.QuotientDuality
