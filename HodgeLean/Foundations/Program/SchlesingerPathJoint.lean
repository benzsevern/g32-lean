import HodgeLean.Foundations.Program.SchlesingerPathFlat

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65p_local_parameter_ode (E P : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    (F : P × (ℂ × E) → E) (p₀ : P) (c : ℂ) (y₀ : E)
    (hF : AnalyticAt ℂ F (p₀, (c, y₀))) :
    ∃ ρ σ : ℝ, 0 < ρ ∧ 0 < σ ∧ ∃ y : P × ℂ → E,
      AnalyticOnNhd ℂ y (ball p₀ ρ ×ˢ ball c σ) ∧
      ∀ p ∈ ball p₀ ρ, y (p, c) = y₀ ∧
        ∀ z ∈ ball c σ, HasDerivAt (fun w ↦ y (p, w)) (F (p, (z, y (p, z)))) z := by
  have hb : ∀ᶠ q in 𝓝 (p₀, (c, y₀)), ‖F q‖ < ‖F (p₀, (c, y₀))‖ + 1 :=
    hF.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp (hF.eventually_analyticAt.and hb)
  have hsub : ball p₀ ε ×ˢ (ball c ε ×ˢ ball y₀ ε) ⊆ ball (p₀, (c, y₀)) ε := by
    intro q hq
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using
      (show dist q.1 p₀ < ε ∧ dist q.2.1 c < ε ∧ dist q.2.2 y₀ < ε from
        ⟨hq.1, hq.2.1, hq.2.2⟩)
  have hM : 0 ≤ ‖F (p₀, (c, y₀))‖ + 1 := by positivity
  obtain ⟨Y, hY, hs⟩ := b65_holomorphic_ode_parameters E P F p₀ c y₀ ε ε ε
    (‖F (p₀, (c, y₀))‖ + 1) hε hε hε hM
    (fun q hq ↦ (he (hsub hq)).1) (fun q hq ↦ (he (hsub hq)).2.le)
  have hσ : 0 < b65_radius ε ε (‖F (p₀, (c, y₀))‖ + 1) := by
    dsimp [b65_radius]
    positivity
  refine ⟨ε, _, hε, hσ, (fun q ↦ Y (q.1, (q.2, y₀))), ?_, ?_⟩
  · intro q hq
    exact (hY (q.1, (q.2, y₀)) ⟨hq.1, hq.2, mem_ball_self (by linarith)⟩).comp
      (f := fun q : P × ℂ ↦ (q.1, (q.2, y₀)))
      (analyticAt_fst.prod (analyticAt_snd.prod analyticAt_const))
  · intro p hp
    obtain ⟨h0, _, hd⟩ := hs p hp y₀ (mem_ball_self (by linarith))
    exact ⟨h0, hd⟩

theorem b65p_local_joint_gauge (E P : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    (S : P × ℂ → E →L[ℂ] E) (p₀ : P) (c : ℂ)
    (hS : AnalyticAt ℂ S (p₀, c)) :
    ∃ ρ σ : ℝ, 0 < ρ ∧ 0 < σ ∧ ∃ Y : P × ℂ → E →L[ℂ] E,
      AnalyticOnNhd ℂ Y (ball p₀ ρ ×ˢ ball c σ) ∧
      ∀ p ∈ ball p₀ ρ, Y (p, c) = 1 ∧
        ∀ z ∈ ball c σ, HasDerivAt (fun w ↦ Y (p, w)) (S (p, z) * Y (p, z)) z := by
  exact b65p_local_parameter_ode (E →L[ℂ] E) P
    (fun q ↦ S (q.1, q.2.1) * q.2.2) p₀ c 1
    ((hS.comp (f := fun q : P × (ℂ × (E →L[ℂ] E)) ↦ (q.1, q.2.1))
      (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd))).mul
      (analyticAt_snd.comp analyticAt_snd))

theorem b65p_verticalCoefficient_joint_analyticAt (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
    (t : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E) (x θ : ℂ)
    (ht : ∀ q, AnalyticAt ℂ (fun z ↦ t z q) θ)
    (hA : ∀ q, AnalyticAt ℂ (fun z ↦ A z q) θ) (hx : ∀ q, x ≠ t θ q) :
    AnalyticAt ℂ (fun w : ℂ × ℂ ↦ b65p_verticalCoefficient E (t w.2)
      (fun q ↦ deriv (fun z ↦ t z q) w.2) (A w.2) w.1) (x, θ) := by
  unfold b65p_verticalCoefficient
  apply AnalyticAt.neg
  apply Finset.analyticAt_fun_sum
  intro q _
  exact (((ht q).deriv.comp (x := (x, θ)) (f := Prod.snd) analyticAt_snd).div
    (analyticAt_fst.sub ((ht q).comp (x := (x, θ)) (f := Prod.snd) analyticAt_snd))
    (sub_ne_zero.mpr (hx q))).smul
    ((hA q).comp (x := (x, θ)) (f := Prod.snd) analyticAt_snd)

theorem b65p_local_vertical_joint_gauge (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] (t : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E)
    (x θ : ℂ) (ht : ∀ q, AnalyticAt ℂ (fun z ↦ t z q) θ)
    (hA : ∀ q, AnalyticAt ℂ (fun z ↦ A z q) θ) (hx : ∀ q, x ≠ t θ q) :
    ∃ ρ σ : ℝ, 0 < ρ ∧ 0 < σ ∧ ∃ Y : ℂ × ℂ → E →L[ℂ] E,
      AnalyticOnNhd ℂ Y (ball x ρ ×ˢ ball θ σ) ∧
      ∀ p ∈ ball x ρ, Y (p, θ) = 1 ∧
        ∀ z ∈ ball θ σ, HasDerivAt (fun w ↦ Y (p, w))
          (b65p_verticalCoefficient E (t z) (fun q ↦ deriv (fun w ↦ t w q) z)
            (A z) p * Y (p, z)) z := by
  exact b65p_local_joint_gauge E ℂ
    (fun w ↦ b65p_verticalCoefficient E (t w.2)
      (fun q ↦ deriv (fun z ↦ t z q) w.2) (A w.2) w.1) x θ
    (b65p_verticalCoefficient_joint_analyticAt E t A x θ ht hA hx)

theorem b65p_flat_gauge_compatibility (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (r : ℝ) (hr : 0 < r) (S H D Y W : ℂ → E →L[ℂ] E)
    (hS : AnalyticOnNhd ℂ S (ball 0 r)) (hY0 : Y 0 = 1) (hW0 : W 0 = 0)
    (hH : ∀ z ∈ ball (0 : ℂ) r,
      HasDerivAt H (D z + S z * H z - H z * S z) z)
    (hY : ∀ z ∈ ball (0 : ℂ) r, HasDerivAt Y (S z * Y z) z)
    (hW : ∀ z ∈ ball (0 : ℂ) r, HasDerivAt W (D z * Y z + S z * W z) z) :
    ∀ z ∈ ball (0 : ℂ) r, W z = H z * Y z - Y z * H 0 := by
  let F : ℂ × (E →L[ℂ] E) → E →L[ℂ] E := fun q ↦ S q.1 * q.2
  let K : ℂ → E →L[ℂ] E := fun z ↦ W z - H z * Y z + Y z * H 0
  have hF : AnalyticAt ℂ F (0, 0) :=
    ((hS 0 (mem_ball_self hr)).comp (x := (0, (0 : E →L[ℂ] E)))
      analyticAt_fst).mul analyticAt_snd
  have hK0 : K 0 = 0 := by simp [K, hY0, hW0]
  have hK (z : ℂ) (hz : z ∈ ball (0 : ℂ) r) :
      HasDerivAt K (F (z, K z)) z := by
    convert ((hW z hz).sub ((hH z hz).mul (hY z hz))).add
      ((hY z hz).mul_const (H 0)) using 1
    dsimp [F, K]
    noncomm_ring
  have he := b65p_ode_unique (E →L[ℂ] E) F 0 hF r hr K (fun _ ↦ 0)
    hK0 rfl hK (fun z _ ↦ by simpa [F] using hasDerivAt_const z (0 : E →L[ℂ] E))
  intro z hz
  have hh : K z = 0 := he hz
  dsimp [K] at hh
  apply sub_eq_zero.mp
  convert hh using 1 <;> abel

end HodgeLean.Foundations.Program
