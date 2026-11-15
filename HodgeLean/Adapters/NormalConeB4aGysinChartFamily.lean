import HodgeLean.Adapters.NormalConeB4aGysinBallRetraction

noncomputable section
namespace HodgeLean.Adapters

/-- A compact normal ball in a partial chart has a global continuous
disk family equal to the inverse chart for all sufficiently small parameters. -/
theorem a3b4a_gysin_chart_continuous_disk_family
    {Y : Type*} [TopologicalSpace Y] {n c : ℕ}
    (Φ : OpenPartialHomeomorph Y ((Fin n → ℂ) × (Fin c → ℂ)))
    (ρ : ℝ) (hball : ∀ v ∈ Metric.closedBall (0 : Fin c → ℂ) ρ,
      ((0 : Fin n → ℂ), v) ∈ Φ.target) :
    ∃ (F : C((Fin n → ℂ) × (Fin c → ℂ), Y)) (δ : ℝ), 0 < δ ∧
      ∀ a : Fin n → ℂ, ‖a‖ < δ → ∀ v ∈ Metric.closedBall (0 : Fin c → ℂ) ρ,
        (a, v) ∈ Φ.target ∧ F (a, v) = Φ.symm (a, v) := by
  by_cases hr : 0 ≤ ρ
  · have hzero : ({(0 : Fin n → ℂ)} ×ˢ Metric.closedBall (0 : Fin c → ℂ) ρ) ⊆ Φ.target := by
      rintro ⟨a, v⟩ ⟨ha, hv⟩
      have ha' : a = 0 := ha
      subst a
      exact hball v hv
    obtain ⟨U, V, hU, _, h0U, hKV, hUV⟩ := generalized_tube_lemma
      (isCompact_singleton (x := (0 : Fin n → ℂ)))
      (isCompact_closedBall (0 : Fin c → ℂ) ρ) Φ.open_target hzero
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU 0 (h0U (Set.mem_singleton 0))
    obtain ⟨P, hPnorm, hPfix⟩ := a3b4a_gysin_exists_closedBall_retraction
      (E := Fin n → ℂ) (ε / 2) (half_pos hε).le
    obtain ⟨Q, hQnorm, hQfix⟩ := a3b4a_gysin_exists_closedBall_retraction
      (E := Fin c → ℂ) ρ hr
    let t : C((Fin n → ℂ) × (Fin c → ℂ), (Fin n → ℂ) × (Fin c → ℂ)) :=
      ⟨fun z => (P z.1, Q z.2),
        (P.continuous.comp continuous_fst).prodMk (Q.continuous.comp continuous_snd)⟩
    have ht (z : (Fin n → ℂ) × (Fin c → ℂ)) : t z ∈ Φ.target := by
      apply hUV
      refine ⟨hεU ?_, hKV ?_⟩
      · rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_le_of_lt (hPnorm z.1) (half_lt_self hε)
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact hQnorm z.2
    let F : C((Fin n → ℂ) × (Fin c → ℂ), Y) :=
      ⟨fun z => Φ.symm (t z), Φ.continuousOn_symm.comp_continuous t.continuous ht⟩
    refine ⟨F, ε / 2, half_pos hε, ?_⟩
    intro a ha v hv
    have hvnorm : ‖v‖ ≤ ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    have heq : t (a, v) = (a, v) := Prod.ext (hPfix a ha.le) (hQfix v hvnorm)
    refine ⟨?_, ?_⟩
    · have h := ht (a, v)
      rwa [heq] at h
    · change Φ.symm (t (a, v)) = Φ.symm (a, v)
      rw [heq]
  · refine ⟨⟨fun _ => Φ.symm (0 : (Fin n → ℂ) × (Fin c → ℂ)), continuous_const⟩,
      1, zero_lt_one, ?_⟩
    intro a _ v hv
    have hv' : dist v 0 ≤ ρ := hv
    exact (hr ((dist_nonneg : 0 ≤ dist v 0).trans hv')).elim

end HodgeLean.Adapters
