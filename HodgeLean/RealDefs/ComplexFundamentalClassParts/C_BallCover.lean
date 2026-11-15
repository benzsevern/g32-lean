import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology

/-! # Covers of a compact set by small closed balls, and restriction in stages

A compact `A` inside an open `W` of a finite-dimensional normed space is covered by finitely many
closed balls centred in `A` whose union stays inside `W` (Hatcher, *Algebraic Topology*,
Lemma 3.27, step (4)). Restriction of local homology along `Z ⊆ W ⊆ U` factors through `W`.
-/

open CategoryTheory AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

/-- A compact subset of an open set of a pseudometric space is covered by finitely many closed
balls of one positive radius, centred in the compact set, whose union lies in the open set. -/
theorem C_exists_closedBall_cover {E : Type} [PseudoMetricSpace E] {A W : Set E}
    (hA : IsCompact A) (hW : IsOpen W) (hAW : A ⊆ W) :
    ∃ (m : ℕ) (c : Fin m → E) (δ : ℝ), 0 < δ ∧ (∀ j, c j ∈ A) ∧
      A ⊆ ⋃ j, Metric.closedBall (c j) δ ∧ (⋃ j, Metric.closedBall (c j) δ) ⊆ W := by
  obtain ⟨δ, hδ, hδW⟩ := hA.exists_cthickening_subset_open hW hAW
  obtain ⟨t, htA, hAt⟩ := hA.elim_nhds_subcover (fun x => Metric.ball x δ)
    (fun x _ => Metric.ball_mem_nhds x hδ)
  let e : Fin t.card ≃ t := t.equivFin.symm
  refine ⟨t.card, fun j => (e j).1, δ, hδ, fun j => htA _ (e j).2, ?_, ?_⟩
  · intro y hy
    have := hAt hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hx, hyx⟩ := this
    simp only [Set.mem_iUnion]
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    simp only [Equiv.apply_symm_apply]
    exact Metric.ball_subset_closedBall hyx
  · refine Set.iUnion_subset fun j => ?_
    exact (Metric.closedBall_subset_cthickening (htA _ (e j).2) δ).trans hδW

/-- Restriction of local homology along `Z ⊆ W ⊆ U` is restriction to `W` followed by
restriction to `Z`. -/
theorem C_relativeHomologyMap_restrict_trans {M : Type} [TopologicalSpace M] {Z W U : Set M}
    (hZW : Z ⊆ W) (hWU : W ⊆ U) (i : ℕ)
    (α : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Uᶜ) i) :
    relativeHomologyMap ℚ i (supportInclusionPairMap (TopCat.of M) (hZW.trans hWU)) α =
      relativeHomologyMap ℚ i (supportInclusionPairMap (TopCat.of M) hZW)
        (relativeHomologyMap ℚ i (supportInclusionPairMap (TopCat.of M) hWU) α) := by
  rw [supportInclusionPairMap_trans, relativeHomologyMap_comp]
  rfl

end HodgeLean.RealDefs
