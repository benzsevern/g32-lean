import HodgeLean.Foundations.QuotientDuality.ProperCycleFlatSupportPartialChart
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-! # Actual open parametrizations inside chart sources
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- Every point of an actual normed chart lies in the image of an open parametrization by its full model space, with image contained in the original source.
Source: OpenPartialHomeomorph.univBall and the original chart inverse.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_open_parametrization
    (X : TopCat.{0}) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : OpenPartialHomeomorph X E) (x : X) (hx : x ∈ c.source) :
    ∃ j : TopCat.of E ⟶ X, IsOpenEmbedding j ∧
      (∀ y, j y ∈ c.source) ∧ j 0 = x := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c x) (c.map_source hx)
  let b := OpenPartialHomeomorph.univBall (c x) r
  let a := b.trans c.symm
  have hsrc : a.source = Set.univ := by
    refine Set.eq_univ_of_forall fun v => ⟨by simp [b], ?_⟩
    apply hball
    rw [← OpenPartialHomeomorph.univBall_target (c x) hr]
    exact b.map_source (by simp [b])
  let j : TopCat.of E ⟶ X := TopCat.ofHom ⟨a, (a.isOpenEmbedding hsrc).continuous⟩
  refine ⟨j, a.isOpenEmbedding hsrc, ?_, ?_⟩
  · intro y
    exact (a.map_source (hsrc ▸ Set.mem_univ y)).1
  · change c.symm (b 0) = x
    rw [show b 0 = c x from OpenPartialHomeomorph.univBall_apply_zero (c x) r]
    exact c.left_inv hx

end HodgeLean.Foundations.QuotientDuality
