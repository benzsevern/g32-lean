import HodgeLean.Foundations.Program.ComponentTransportNormalized
import HodgeLean.Foundations.Program.RadialTransportComparison

/-! # Quantitative control for normalized transport -/
noncomputable section
open Set Topology
namespace HodgeLean.Foundations.Program

/-- A compact configuration track has a uniform positive transport radius.
Source: `b65y_radius_continuousOn`; the extreme value theorem. -/
theorem b65v_uniform_radius (γ : C(unitInterval, Fin 10 → ℂ))
    (hγ : ∀ t, γ t ∈ b6_chart) :
    ∃ r : ℝ, 0 < r ∧ ∀ t, r ≤ b6t_radius (γ t) := by
  have hc : Continuous fun t ↦ b6t_radius (γ t) :=
    b65y_radius_continuousOn.comp_continuous γ.continuous hγ
  obtain ⟨t, _, ht⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  exact ⟨_, (b6t_discs _ (hγ t)).1, fun s ↦ ht (Set.mem_univ s)⟩

/-- Rapid escape and suffix speed control give convex regions for every valid cell,
including a cell meeting the escape junction.
Source: `b65v_escape_step_bound`; `docs/specs/spec-rtc.md`, quantitative reparametrization. -/
theorem b65v_escape_cell_regions (γ : C(unitInterval, Fin 10 → ℂ))
    (hγ : ∀ t, γ t ∈ b6_chart)
    (t₁ : unitInterval) (S r d : ℝ) (hS : 0 ≤ S)
    (hr : S * (t₁ : ℝ) < r) (hd : S * (t₁ : ℝ) < d)
    (V : Set (Fin 10 → ℂ)) (hV : Convex ℝ V) (hchart : V ⊆ b6_chart)
    (hinitial : ∀ t : unitInterval, (t : ℝ) ≤ t₁ → γ t ∈ V)
    (hmargin : Metric.ball (γ t₁) d ⊆ V)
    (hescape : ∀ t : unitInterval, (t₁ : ℝ) ≤ t → γ t ∉ b6t_polydisc (γ 0))
    (hspeed : ∀ s t : unitInterval, (t₁ : ℝ) ≤ s → (t₁ : ℝ) ≤ t →
      dist (γ s) (γ t) ≤ S * |(s : ℝ) - t|)
    (hradius : ∀ t : unitInterval, (t₁ : ℝ) ≤ t → r ≤ b6t_radius (γ t))
    (N : ℕ) (hN : 0 < N)
    (hsteps : ∀ k < N, b65y_sample γ N (k + 1) ∈
      b6t_polydisc (b65y_sample γ N k)) :
    ∀ k < N, ∃ W : Set (Fin 10 → ℂ), Convex ℝ W ∧ W ⊆ b6_chart ∧
      ∀ t : unitInterval, (k : ℝ) / N ≤ (t : ℝ) →
        (t : ℝ) ≤ ((k : ℝ) + 1) / N → γ t ∈ W := by
  have hsmall := b65v_escape_step_bound γ t₁ hescape N hN hsteps
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  intro k hk
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk.le
  let s : unitInterval := ⟨(k : ℝ) / N, by
    exact ⟨by positivity, (div_le_one hNr).mpr hkN⟩⟩
  have hs : (s : ℝ) = (k : ℝ) / N := rfl
  by_cases hstart : (s : ℝ) < t₁
  · refine ⟨V, hV, hchart, fun t hleft hright ↦ ?_⟩
    by_cases ht : (t : ℝ) ≤ t₁
    · exact hinitial t ht
    · apply hmargin
      change dist (γ t) (γ t₁) < d
      have ht₁ : (t₁ : ℝ) ≤ t := le_of_not_ge ht
      have htime : (t : ℝ) - t₁ < (t₁ : ℝ) := by
        rw [add_div] at hright
        linarith
      have hdist := hspeed t t₁ ht₁ le_rfl
      rw [abs_of_nonneg (sub_nonneg.mpr ht₁)] at hdist
      exact lt_of_le_of_lt hdist (lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        htime.le hS) hd)
  · have hst : (t₁ : ℝ) ≤ s := le_of_not_gt hstart
    refine ⟨b6t_polydisc (γ s), ?_,
      (b6t_polydisc_neighbourhood _ (hγ s)).2.2.2, ?_⟩
    · intro x hx y hy a b ha hb hab i
      exact convex_ball (γ s i) (b6t_radius (γ s)) (hx i) (hy i) ha hb hab
    · intro t hleft hright i
      change dist (γ t i) (γ s i) < b6t_radius (γ s)
      have hst' : (s : ℝ) ≤ t := hleft
      have ht₁ : (t₁ : ℝ) ≤ t := hst.trans hst'
      have htime : (t : ℝ) - s ≤ (1 : ℝ) / N := by
        rw [add_div] at hright
        linarith
      have hdist := hspeed t s ht₁ hst
      rw [abs_of_nonneg (sub_nonneg.mpr hst')] at hdist
      calc
        dist (γ t i) (γ s i) ≤ dist (γ t) (γ s) := dist_le_pi_dist _ _ i
        _ ≤ S * ((t : ℝ) - s) := hdist
        _ ≤ S * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left htime hS
        _ ≤ S * (t₁ : ℝ) := mul_le_mul_of_nonneg_left hsmall.le hS
        _ < r := hr
        _ ≤ b6t_radius (γ s) := hradius s hst

/-- The certificate endpoint is outside the initial disc product, already in coordinate zero.
Source: B65-BRAIDCERT JSON, boxes 0, 6, 8, 10; `b65v_relabelCentre`. -/
theorem b65v_endpoint_outside (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    b6t_radius mr_base < dist (b65v_relabelCentre p 0) (mr_base 0) := by
  have h10 := hp 0
  have h2 := hp 8
  have h8 := hp 10
  have h11 := hp 6
  norm_num [b65b_boxIndex, b65b_boxCentre, b65b_boxFibre] at h10 h2 h8 h11
  have h10r := abs_lt.mp h10.1
  have h10i := abs_lt.mp h10.2.1
  have h2r := abs_lt.mp h2.1
  have h2i := abs_lt.mp h2.2.1
  have h8r := abs_lt.mp h8.1
  have h8i := abs_lt.mp h8.2.1
  have h11r := abs_lt.mp h11.1
  have hp2 : 1 < ‖p 2‖ := by
    have := Complex.re_le_norm (p 2)
    linarith
  have hp8a : 7 < ‖p 8 - p 10‖ := by
    have := Complex.re_le_norm (p 8 - p 10)
    simp only [Complex.sub_re] at this
    linarith
  have hp2n : ‖p 2‖ < 2 := by
    have := Complex.norm_le_abs_re_add_abs_im (p 2)
    rw [abs_of_pos (by linarith : 0 < (p 2).re),
      abs_of_neg (by linarith : (p 2).im < 0)] at this
    linarith
  have hp8n : ‖p 8‖ < 5 := by
    have := Complex.norm_le_abs_re_add_abs_im (p 8)
    rw [abs_of_neg (by linarith : (p 8).re < 0),
      abs_of_pos (by linarith : 0 < (p 8).im)] at this
    linarith
  have hp10n : ‖p 10‖ < 9 := by
    have := Complex.norm_le_abs_re_add_abs_im (p 10)
    rw [abs_of_neg (by linarith : (p 10).re < 0)] at this
    linarith [h10.2.1]
  have h2ne : p 2 ≠ 0 := norm_pos_iff.mp (by linarith)
  have h8ane : p 8 - p 10 ≠ 0 := norm_pos_iff.mp (by linarith)
  have h11ne : p 11 ≠ 0 := by
    intro hz
    simp only [hz, Complex.zero_re] at h11r
    linarith
  have h11ane : p 11 - p 10 ≠ 0 := by
    intro hz
    have he := congrArg Complex.re (sub_eq_zero.mp hz)
    linarith
  have hratio : b65z_centre p 2 / b65z_centre p 8 =
      (p 2 - p 10) * p 8 / (p 2 * (p 8 - p 10)) := by
    simp only [b65z_centre, b65p_curve, b65p_chartPoint, b65p_moving, b65p_poles,
      Sum.elim_inr, zero_mul, add_zero, b65s_normalize]
    change ((p 2 - p 10) * p 11 / (p 2 * (p 11 - p 10))) /
      ((p 8 - p 10) * p 11 / (p 8 * (p 11 - p 10))) = _
    have h8ne : p 8 ≠ 0 := by
      intro hz
      simp only [hz, Complex.zero_im] at h8i
      linarith
    field_simp [h2ne, h8ane, h11ne, h11ane, h8ne]
  have hratioNorm : ‖b65z_centre p 2 / b65z_centre p 8‖ < 8 := by
    rw [hratio, norm_div, norm_mul, norm_mul]
    apply (div_lt_iff₀ (mul_pos (by linarith) (by linarith))).mpr
    have hdiff : ‖p 2 - p 10‖ < 11 :=
      lt_of_le_of_lt (norm_sub_le _ _) (by linarith)
    nlinarith [norm_nonneg (p 2 - p 10), norm_nonneg (p 8)]
  have hτ : b65u_endpointPerm.symm ((0 : Fin 10).castAdd 3) =
      (2 : Fin 10).castAdd 3 := by decide +kernel
  have hnorm : ‖b65v_relabelCentre p 0‖ < 9 := by
    simp only [b65v_relabelCentre, hτ, Fin.append_left]
    have hh := norm_sub_le (1 : ℂ) (b65z_centre p 2 / b65z_centre p 8)
    norm_num only [norm_one] at hh
    linarith
  have hradius : b6t_radius mr_base < 1 := by
    have hsum : 0 ≤ ∑ i : Fin 10, (‖mr_base i‖⁻¹ + ‖mr_base i - 1‖⁻¹ +
        ∑ j : Fin 10, if i = j then 0 else (dist (mr_base i) (mr_base j))⁻¹) := by
      apply Finset.sum_nonneg
      intro i _
      have : 0 ≤ ∑ j : Fin 10, if i = j then (0 : ℝ) else
          (dist (mr_base i) (mr_base j))⁻¹ := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs <;> positivity
      positivity
    unfold b6t_radius
    apply (inv_lt_one₀ (by positivity)).mpr
    linarith
  have hbase : ‖mr_base 0‖ = 12 := by norm_num [mr_base]
  have hdist : 3 < dist (b65v_relabelCentre p 0) (mr_base 0) := by
    have := norm_le_norm_sub_add (mr_base 0) (b65v_relabelCentre p 0)
    rw [norm_sub_rev] at this
    rw [dist_eq_norm]
    linarith
  linarith

/-- The initial disc product has a larger open convex neighbourhood inside the chart.
Source: `b6t_discs`; compactness of finite products of discs. -/
theorem b65v_polydisc_buffer (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) :
    ∃ R : ℝ, b6t_radius c < R ∧ Metric.ball c R ⊆ b6_chart := by
  have hr := (b6t_discs c hc).1
  have hcoord := (b6_chart_coordinates c).mp hc
  have hK : Metric.closedBall c (b6t_radius c) ⊆ b6_chart := by
    intro z hz
    have hz' := (dist_pi_le_iff hr.le).mp hz
    apply (b6_chart_coordinates z).mpr
    constructor
    · intro i j he
      by_contra hij
      apply Set.disjoint_left.mp ((b6t_discs c hc).2.2 hij)
        (show z i ∈ Metric.closedBall (c i) (b6t_radius c) from hz' i)
      simpa only [he, Metric.mem_closedBall] using hz' j
    · intro i
      constructor
      · intro he
        exact ((b6t_discs c hc).2.1 i).1 (he ▸ hz' i)
      · intro he
        exact ((b6t_discs c hc).2.1 i).2 (he ▸ hz' i)
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall c (b6t_radius c)).exists_cthickening_subset_open
    b6_chart_open hK
  refine ⟨b6t_radius c + δ, by linarith, ?_⟩
  apply Set.Subset.trans Metric.ball_subset_closedBall
  rw [add_comm (b6t_radius c) δ, ← cthickening_closedBall hδ.le hr.le]
  exact hsub

/-- Prepend a straight escape and move the suffix outside the initial disc product,
retaining the relative class of any given chart path.
Source: `b65v_polydisc_buffer`; `rtc_avoidance`; Hatcher, Algebraic Topology, §1.2. -/
theorem b65v_escape_avoidance {a b : b6_chart} (α : Path a b)
    (hb : ¬ ∀ i, dist (b.val i) (a.val i) ≤ b6t_radius a.val) :
    ∃ V : Set (Fin 10 → ℂ), IsOpen V ∧ Convex ℝ V ∧ V ⊆ b6_chart ∧
      ∃ q : b6_chart, ∃ E : Path a q, ∃ σ : Path q b,
        α.Homotopic (E.trans σ) ∧
        (∀ t, (E t).val ∈ V) ∧
        (∀ t, (E t).val = (1 - (t : ℝ)) • a.val + (t : ℝ) • q.val) ∧
        ∀ t, ¬ ∀ i, dist ((σ t).val i) (a.val i) ≤ b6t_radius a.val := by
  obtain ⟨R, hR, hchart⟩ := b65v_polydisc_buffer a.val a.property
  have hr := (b6t_discs a.val a.property).1
  let u : ℝ := (b6t_radius a.val + R) / 2
  have hu : 0 < u := by dsimp [u]; linarith
  have hur : b6t_radius a.val < u := by dsimp [u]; linarith
  have huR : u < R := by dsimp [u]; linarith
  let qv : Fin 10 → ℂ := fun i ↦ a.val i + (u : ℂ)
  have hdist (i : Fin 10) : dist (qv i) (a.val i) = u := by
    simp only [qv, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hu]
  have hq : qv ∈ Metric.ball a.val R := by
    exact (dist_pi_lt_iff (hr.trans hR)).mpr (fun i ↦ (hdist i).trans_lt huR)
  let q : b6_chart := ⟨qv, hchart hq⟩
  have hqout : ¬ ∀ i, dist (q.val i) (a.val i) ≤ b6t_radius a.val := by
    intro hh
    have hh0 := hh 0
    change dist (qv 0) (a.val 0) ≤ _ at hh0
    rw [hdist] at hh0
    linarith
  have haV : a.val ∈ Metric.ball a.val R := Metric.mem_ball_self (hr.trans hR)
  have hseg (t : unitInterval) :
      (1 - (t : ℝ)) • a.val + (t : ℝ) • q.val ∈ Metric.ball a.val R :=
    convex_ball a.val R haV hq (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel _ _)
  let E : Path a q :=
    { toFun := fun t ↦ ⟨(1 - (t : ℝ)) • a.val + (t : ℝ) • q.val, hchart (hseg t)⟩
      continuous_toFun := by fun_prop
      source' := by apply Subtype.ext; simp
      target' := by apply Subtype.ext; simp }
  have hK : {z : Fin 10 → ℂ | ∀ i, dist (z i) (a.val i) ≤ b6t_radius a.val} ⊆
      Metric.ball a.val R := by
    intro z hz
    exact (dist_pi_lt_iff (hr.trans hR)).mpr (fun i ↦ (hz i).trans_lt hR)
  obtain ⟨σ, hσ, hout⟩ := rtc_avoidance a.val (b6t_radius a.val) hr
    (Metric.ball a.val R) Metric.isOpen_ball (convex_ball _ _) hchart hK
    (E.symm.trans α) hqout hb
  refine ⟨Metric.ball a.val R, Metric.isOpen_ball, convex_ball _ _, hchart,
    q, E, σ, ?_, hseg, fun _ ↦ rfl, hout⟩
  have hcancel : (E.trans (E.symm.trans α)).Homotopic α :=
    (Path.Homotopic.trans_assoc E E.symm α).symm.trans
      (((Path.Homotopic.trans_symm E).hcomp (Path.Homotopic.refl α)).trans
        (Path.Homotopic.refl_trans α))
  exact hcancel.symm.trans ((Path.Homotopic.refl E).hcomp hσ)

/-- A suffix modulus of continuity suffices for cell control; no speed estimate is needed.
Source: `b65v_escape_step_bound`; the convex-region subdivision argument in spec-rtc. -/
theorem b65v_escape_cell_regions_modulus (γ : C(unitInterval, Fin 10 → ℂ))
    (hγ : ∀ t, γ t ∈ b6_chart) (t₁ : unitInterval) (r d : ℝ)
    (V : Set (Fin 10 → ℂ)) (hV : Convex ℝ V) (hchart : V ⊆ b6_chart)
    (hinitial : ∀ t : unitInterval, (t : ℝ) ≤ t₁ → γ t ∈ V)
    (hmargin : Metric.ball (γ t₁) d ⊆ V)
    (hescape : ∀ t : unitInterval, (t₁ : ℝ) ≤ t → γ t ∉ b6t_polydisc (γ 0))
    (hlocal : ∀ s t : unitInterval, (t₁ : ℝ) ≤ s → (t₁ : ℝ) ≤ t →
      |(s : ℝ) - t| < t₁ → dist (γ s) (γ t) < min r d)
    (hradius : ∀ t : unitInterval, (t₁ : ℝ) ≤ t → r ≤ b6t_radius (γ t))
    (N : ℕ) (hN : 0 < N)
    (hsteps : ∀ k < N, b65y_sample γ N (k + 1) ∈
      b6t_polydisc (b65y_sample γ N k)) :
    ∀ k < N, ∃ W : Set (Fin 10 → ℂ), Convex ℝ W ∧ W ⊆ b6_chart ∧
      ∀ t : unitInterval, (k : ℝ) / N ≤ (t : ℝ) →
        (t : ℝ) ≤ ((k : ℝ) + 1) / N → γ t ∈ W := by
  have hsmall := b65v_escape_step_bound γ t₁ hescape N hN hsteps
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  intro k hk
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk.le
  let s : unitInterval := ⟨(k : ℝ) / N,
    ⟨by positivity, (div_le_one hNr).mpr hkN⟩⟩
  have hs : (s : ℝ) = (k : ℝ) / N := rfl
  by_cases hstart : (s : ℝ) < t₁
  · refine ⟨V, hV, hchart, fun t hleft hright ↦ ?_⟩
    by_cases ht : (t : ℝ) ≤ t₁
    · exact hinitial t ht
    · apply hmargin
      have ht₁ : (t₁ : ℝ) ≤ t := le_of_not_ge ht
      have htime : |(t : ℝ) - t₁| < (t₁ : ℝ) := by
        rw [abs_of_nonneg (sub_nonneg.mpr ht₁)]
        rw [add_div] at hright
        linarith
      exact (hlocal t t₁ ht₁ le_rfl htime).trans_le (min_le_right _ _)
  · have hst : (t₁ : ℝ) ≤ s := le_of_not_gt hstart
    refine ⟨b6t_polydisc (γ s), ?_,
      (b6t_polydisc_neighbourhood _ (hγ s)).2.2.2, ?_⟩
    · intro x hx y hy a b ha hb hab i
      exact convex_ball (γ s i) (b6t_radius (γ s)) (hx i) (hy i) ha hb hab
    · intro t hleft hright i
      have hst' : (s : ℝ) ≤ t := hleft
      have htime : |(t : ℝ) - s| < (t₁ : ℝ) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hst')]
        rw [add_div] at hright
        linarith
      exact (dist_le_pi_dist _ _ i).trans_lt
        (((hlocal t s (hst.trans hst') hst htime).trans_le (min_le_left _ _)).trans_le
          (hradius s hst))

end HodgeLean.Foundations.Program
