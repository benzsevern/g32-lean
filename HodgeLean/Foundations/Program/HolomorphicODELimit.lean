import HodgeLean.Foundations.Program.HolomorphicODECauchy

noncomputable section
open Set Metric Filter Topology
namespace HodgeLean.Foundations.Program

theorem b65_uniform_limit_analytic {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set E} (hU : IsOpen U) {f : ℕ → E → F} {g : E → F}
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) U) (hg : TendstoUniformlyOn f g atTop U) :
    AnalyticOnNhd ℂ g U := by
  intro z hz
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hz
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hball : ∀ x ∈ ball z δ, closedBall x δ ⊆ U := by
    intro x hx v hv
    apply hεU
    rw [mem_ball]
    have ht := dist_triangle v x z
    have hv' := mem_closedBall.mp hv
    have hx' := mem_ball.mp hx
    dsimp [δ] at hv' hx'
    linarith
  have hsmall : ball z δ ⊆ U := fun x hx ↦ hball x hx (mem_closedBall_self hδ.le)
  have hc : UniformCauchySeqOn (fun n x ↦ fderiv ℂ (f n) x) atTop (ball z δ) := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro η hη
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hg.uniformCauchySeqOn (η * δ / 2) (by positivity)
    refine ⟨N, fun m hm n hn x hx ↦ ?_⟩
    have hbound := b65_norm_fderiv_le hδ (by positivity : 0 ≤ η * δ / 2)
      (((hf m).sub (hf n)).mono (hball x hx))
      (fun v hv ↦ by simpa [dist_eq_norm] using (hN m hm n hn v (hball x hx hv)).le)
    have hdm := (hf m x (hsmall hx)).differentiableAt
    have hdn := (hf n x (hsmall hx)).differentiableAt
    rw [fderiv_sub hdm hdn] at hbound
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hbound (by rw [div_lt_iff₀ hδ]; nlinarith)
  let G : E → E →L[ℂ] F := fun x ↦ limUnder atTop (fun n ↦ fderiv ℂ (f n) x)
  have hG : TendstoUniformlyOn (fun n x ↦ fderiv ℂ (f n) x) G atTop (ball z δ) :=
    hc.tendstoUniformlyOn_of_tendsto (fun x hx ↦ (hc.cauchySeq hx).tendsto_limUnder)
  have hd : DifferentiableOn ℂ g (ball z δ) := by
    intro x hx
    exact (hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hG
      (fun n v hv ↦ (hf n v (hsmall hv)).differentiableAt.hasFDerivAt)
      (fun v hv ↦ hg.tendsto_at (hsmall hv)) hx).differentiableAt.differentiableWithinAt
  exact b65_spec_analyticOnNhd_of_differentiableOn_aux isOpen_ball hd z (mem_ball_self hδ)

theorem b65_geometric_uniform_limit {X F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    {U : Set X} {f : ℕ → X → F} {C q : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1)
    (hf : ∀ n x, x ∈ U → ‖f (n + 1) x - f n x‖ ≤ C * q ^ n) :
    ∃ g : X → F, TendstoUniformlyOn f g atTop U := by
  let g : X → F := fun x ↦ limUnder atTop (fun n ↦ f n x)
  have hd (x : X) (hx : x ∈ U) (n : ℕ) :
      dist (f n x) (f (n + 1) x) ≤ C * q ^ n := by
    simpa [dist_eq_norm, norm_sub_rev] using hf n x hx
  have ht (x : X) (hx : x ∈ U) : Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) :=
    (cauchySeq_of_le_geometric q C hq (hd x hx)).tendsto_limUnder
  have hqpow : Tendsto (fun n : ℕ ↦ C * q ^ n / (1 - q)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq).const_mul C).div_const (1 - q)
  refine ⟨g, Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro ε hε
  filter_upwards [hqpow.eventually (gt_mem_nhds hε)] with n hn x hx
  rw [dist_comm]
  exact (dist_le_of_le_geometric_of_tendsto q C hq (hd x hx) (ht x hx) n).trans_lt hn

end HodgeLean.Foundations.Program
