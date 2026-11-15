import HodgeLean.Foundations.Program.SchoenTowerT11bLocalConnectedness

/-! Compact connected Boolean neighborhoods in closed realizations.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open scoped Topology

/-- A point of a closed Boolean realization has a compact connected Boolean neighborhood inside each specified positive closed ball.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compact connected local selection step. -/
theorem s2v_t11b_closed_formula_connected_neighborhood {n : ℕ}
    (f : s2v_t11b_Formula n) (hf : IsClosed f.realize) (x : f.realize)
    (r : ℝ) (hr : 0 < r) :
    ∃ g : s2v_t11b_Formula n,
      IsCompact g.realize ∧ IsConnected g.realize ∧ g.realize ⊆ f.realize ∧
      g.realize ⊆ Metric.closedBall x.val r ∧
      {y : f.realize | y.val ∈ g.realize} ∈ 𝓝 x := by
  classical
  obtain ⟨b, hb⟩ := s2v_t11b_closedBall_formula x.val r hr.le
  let B := s2v_t11b_Formula.inter f b
  have hB : IsCompact B.realize := by
    change IsCompact (f.realize ∩ b.realize)
    rw [hb]
    exact (isCompact_closedBall x.val r).inter_left hf
  letI : CompactSpace B.realize := isCompact_iff_compactSpace.mp hB
  letI := s2v_t11b_formula_finite_components B
  let a : B.realize := ⟨x.val, x.property, hb.symm ▸ Metric.mem_closedBall_self hr.le⟩
  obtain ⟨g, hg⟩ := s2v_t11b_compact_component_formula B a isClosed_connectedComponent.isCompact
  have hsub : g.realize ⊆ B.realize := by
    rw [hg]
    rintro y ⟨z, hz, rfl⟩
    exact z.property
  obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.mp (s2v_t11b_component_clopen_of_finite a).isOpen
  have hxO : x.val ∈ O := by
    have ha : a ∈ connectedComponent a := mem_connectedComponent
    rw [← hpre] at ha
    exact ha
  refine ⟨g, ?_, ?_, fun y hy => (hsub hy).1, ?_, ?_⟩
  · rw [hg]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  · rw [hg]
    exact isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  · intro y hy
    exact hb ▸ (hsub hy).2
  · apply Filter.mem_of_superset (Filter.inter_mem
      ((hO.preimage continuous_subtype_val).mem_nhds hxO) (Metric.closedBall_mem_nhds x hr))
    intro y hy
    have hyB : y.val ∈ B.realize := ⟨y.property, hb.symm ▸ hy.2⟩
    rw [Set.mem_setOf_eq, hg]
    refine ⟨⟨y.val, hyB⟩, ?_, rfl⟩
    rw [← hpre]
    exact hy.1

end HodgeLean.Foundations.Program
