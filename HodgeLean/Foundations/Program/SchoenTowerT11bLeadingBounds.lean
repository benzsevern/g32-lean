import HodgeLean.Foundations.Program.SchoenTowerT11bRootBounds

/-! Root bounds for families whose leading coefficient stays nonzero.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open scoped NNReal Topology

/-- A nonvanishing leading coefficient gives uniform root bounds on compact parameter sets.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, bounded root-section step. -/
theorem s2v_t11b_family_root_bound_of_leadingCoeff
    (P : Polynomial (Polynomial ℝ)) (K : Set ℝ) (hK : IsCompact K)
    (hlead : ∀ t ∈ K, P.leadingCoeff.eval t ≠ 0) :
    ∃ B : ℝ≥0, 0 < B ∧ ∀ t ∈ K, ∀ x : ℝ,
      P.eval₂ (Polynomial.evalRingHom t) x = 0 → ‖x‖₊ < B := by
  classical
  have hc : ∀ i : Fin P.natDegree, ∃ M : ℝ≥0,
      ∀ t ∈ K, ‖(P.coeff i.val).eval t / P.leadingCoeff.eval t‖₊ ≤ M := by
    intro i
    have hcont := ((P.coeff i.val).continuous.continuousOn.div
      P.leadingCoeff.continuous.continuousOn hlead).nnnorm
    obtain ⟨M, hM⟩ := hK.bddAbove_image hcont
    exact ⟨M, fun t ht => hM ⟨t, ht, rfl⟩⟩
  choose M hM using hc
  let B₀ : ℝ≥0 := Finset.univ.sup M
  let B : ℝ≥0 := B₀ + 1
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro t ht x hx
  have hlt : 0 < ‖P.leadingCoeff.eval t‖₊ := nnnorm_pos.mpr (hlead t ht)
  have hdeg := P.natDegree_map_of_leadingCoeff_ne_zero (Polynomial.evalRingHom t)
    (hlead t ht)
  have hl := P.leadingCoeff_map_of_leadingCoeff_ne_zero (Polynomial.evalRingHom t)
    (hlead t ht)
  have hbound : (P.map (Polynomial.evalRingHom t)).cauchyBound ≤ B := by
    rw [Polynomial.cauchyBound, hdeg, hl]
    apply add_le_add ?_ le_rfl
    apply (div_le_iff₀ hlt).mpr
    apply Finset.sup_le
    intro i hi
    rw [Polynomial.coeff_map]
    have hm := (hM ⟨i, Finset.mem_range.mp hi⟩ t ht).trans
      (Finset.le_sup (f := M) (Finset.mem_univ _))
    rw [nnnorm_div] at hm
    exact (div_le_iff₀ hlt).mp hm
  have hroot : (P.map (Polynomial.evalRingHom t)).IsRoot x := by
    simpa only [Polynomial.IsRoot.def, ← Polynomial.eval₂_eq_eval_map] using hx
  have hne : P.map (Polynomial.evalRingHom t) ≠ 0 := by
    intro hz
    have hl' := hl
    rw [hz, Polynomial.leadingCoeff_zero] at hl'
    exact hlead t ht hl'.symm
  exact (hroot.norm_lt_cauchyBound hne).trans_le hbound

/-- Without a degree drop, nearby real roots remain in every open neighborhood of the initial roots.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, bounded root-section step. -/
theorem s2v_t11b_family_roots_stay_in_of_leadingCoeff
    (P : Polynomial (Polynomial ℝ)) (a : ℝ) (hlead : P.leadingCoeff.eval a ≠ 0)
    (U : Set ℝ) (hU : IsOpen U)
    (hroots : ∀ x : ℝ, P.eval₂ (Polynomial.evalRingHom a) x = 0 → x ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Metric.ball a ε, ∀ x : ℝ,
      P.eval₂ (Polynomial.evalRingHom t) x = 0 → x ∈ U := by
  have hne : ∀ᶠ t in 𝓝 a, P.leadingCoeff.eval t ≠ 0 :=
    (P.leadingCoeff.continuous.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hlead
  obtain ⟨r, hr, hlead_near⟩ := Metric.eventually_nhds_iff.mp hne
  have hlead_ball : ∀ t ∈ Metric.closedBall a (r / 2), P.leadingCoeff.eval t ≠ 0 := by
    intro t ht
    exact hlead_near ((Metric.mem_closedBall.mp ht).trans_lt (half_lt_self hr))
  obtain ⟨B, _, hB⟩ := s2v_t11b_family_root_bound_of_leadingCoeff P
    (Metric.closedBall a (r / 2)) (isCompact_closedBall a (r / 2)) hlead_ball
  let K : Set ℝ := Metric.closedBall 0 (B : ℝ) \ U
  have hK : IsCompact K := (isCompact_closedBall (0 : ℝ) (B : ℝ)).diff hU
  obtain ⟨s, hs, hno⟩ := s2v_t11b_polynomial_family_compact_root_exclusion P a K hK
    (fun x hx hzero => hx.2 (hroots x hzero))
  refine ⟨min s (r / 2), lt_min hs (half_pos hr), ?_⟩
  intro t ht x hx
  have htK : t ∈ Metric.closedBall a (r / 2) :=
    (Metric.mem_ball.mp ht).le.trans (min_le_right s (r / 2))
  have hxB : x ∈ Metric.closedBall 0 (B : ℝ) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (show ‖x‖ < (B : ℝ) from hB t htK x hx).le
  by_contra hxU
  exact hno t ((Metric.mem_ball.mp ht).trans_le (min_le_left s (r / 2))) x ⟨hxB, hxU⟩ hx

end HodgeLean.Foundations.Program
