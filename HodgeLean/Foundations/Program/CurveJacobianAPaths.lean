import HodgeLean.Foundations.Program.CurveJacobianAPlumbing

/-! # Track B3, lane A: good paths

A good path is a `C¹` map `ℝ → C` that is constant near `0` and near `1`; good paths reverse and
concatenate, segments in charts are good paths, and a connected Riemann surface is connected by good
paths.
-/

noncomputable section

open Manifold Filter Topology Set
open scoped ContDiff TensorProduct

namespace HodgeLean.Foundations.Program

section Paths

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C]

/-- **A good path** from `p` to `q`: a `C¹` map `ℝ → C`, constant near `0` (value `p`) and near
`1` (value `q`). Good paths concatenate to good paths. -/
def b3A_IsGoodPath (γ : ℝ → C) (p q : C) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ ∧ (∀ᶠ t in 𝓝 0, γ t = p) ∧ ∀ᶠ t in 𝓝 1, γ t = q

/-- A good path starts at its initial point. -/
theorem b3A_IsGoodPath.apply_zero {γ : ℝ → C} {p q : C} (h : b3A_IsGoodPath (E := E) γ p q) :
    γ 0 = p := h.2.1.self_of_nhds

/-- A good path ends at its final point. -/
theorem b3A_IsGoodPath.apply_one {γ : ℝ → C} {p q : C} (h : b3A_IsGoodPath (E := E) γ p q) :
    γ 1 = q := h.2.2.self_of_nhds

/-- Constant paths are good. -/
theorem b3A_isGoodPath_const (p : C) : b3A_IsGoodPath (E := E) (fun _ ↦ p) p p :=
  ⟨contMDiff_const, Eventually.of_forall fun _ ↦ rfl, Eventually.of_forall fun _ ↦ rfl⟩

/-- Reparametrizing a `C¹` path by a `C¹` map of `ℝ` gives a `C¹` path. -/
theorem b3A_contMDiff_reparam {γ : ℝ → C} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ 1 σ) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (γ ∘ σ) :=
  hγ.comp hσ.contMDiff

/-- The reverse of a good path is good. -/
theorem b3A_IsGoodPath.symm {γ : ℝ → C} {p q : C} (h : b3A_IsGoodPath (E := E) γ p q) :
    b3A_IsGoodPath (E := E) (fun t ↦ γ (1 - t)) q p := by
  refine ⟨b3A_contMDiff_reparam h.1 (σ := fun t ↦ 1 - t) (contDiff_const.sub contDiff_id),
    ?_, ?_⟩
  · have : Tendsto (fun t : ℝ ↦ 1 - t) (𝓝 0) (𝓝 1) := by
      simpa using (continuous_sub_left (1 : ℝ)).tendsto 0
    exact this.eventually h.2.2
  · have : Tendsto (fun t : ℝ ↦ 1 - t) (𝓝 1) (𝓝 0) := by
      simpa using (continuous_sub_left (1 : ℝ)).tendsto 1
    exact this.eventually h.2.1

/-- The concatenation of good paths is good. -/
theorem b3A_IsGoodPath.trans {γ δ : ℝ → C} {p q r : C} (hγ : b3A_IsGoodPath (E := E) γ p q)
    (hδ : b3A_IsGoodPath (E := E) δ q r) :
    b3A_IsGoodPath (E := E) (fun t ↦ if t ≤ 1 / 2 then γ (2 * t) else δ (2 * t - 1)) p r := by
  have h2 : Continuous (fun t : ℝ ↦ 2 * t) := continuous_const.mul continuous_id
  have h2' : Continuous (fun t : ℝ ↦ 2 * t - 1) := h2.sub continuous_const
  have hγ' : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun t ↦ γ (2 * t)) :=
    b3A_contMDiff_reparam hγ.1 (σ := fun t ↦ 2 * t) (contDiff_const.mul contDiff_id)
  have hδ' : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun t ↦ δ (2 * t - 1)) :=
    b3A_contMDiff_reparam hδ.1 (σ := fun t ↦ 2 * t - 1)
      ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hq1 : ∀ᶠ t in 𝓝 (1 / 2 : ℝ), γ (2 * t) = q := by
    have : Tendsto (fun t : ℝ ↦ 2 * t) (𝓝 (1 / 2)) (𝓝 1) := by
      simpa using h2.tendsto (1 / 2 : ℝ)
    exact this.eventually hγ.2.2
  have hq2 : ∀ᶠ t in 𝓝 (1 / 2 : ℝ), δ (2 * t - 1) = q := by
    have : Tendsto (fun t : ℝ ↦ 2 * t - 1) (𝓝 (1 / 2)) (𝓝 0) := by
      simpa using h2'.tendsto (1 / 2 : ℝ)
    exact this.eventually hδ.2.1
  refine ⟨fun t₀ ↦ ?_, ?_, ?_⟩
  · rcases lt_trichotomy t₀ (1 / 2) with ht | rfl | ht
    · refine (hγ' t₀).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds ht] with t ht'
      exact ite_eq_left (le_of_lt ht')
    · refine (contMDiffAt_const (c := q)).congr_of_eventuallyEq ?_
      filter_upwards [hq1, hq2] with t h1 h2
      split_ifs <;> simp_all
    · refine (hδ' t₀).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds ht] with t ht'
      exact ite_eq_right (not_le.2 ht')
  · have : Tendsto (fun t : ℝ ↦ 2 * t) (𝓝 0) (𝓝 0) := by
      simpa using h2.tendsto (0 : ℝ)
    filter_upwards [this.eventually hγ.2.1, Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)]
      with t h1 h2
    exact (ite_eq_left (le_of_lt h2)).trans h1
  · have : Tendsto (fun t : ℝ ↦ 2 * t - 1) (𝓝 1) (𝓝 1) := by
      have := h2'.tendsto (1 : ℝ)
      norm_num at this
      exact this
    filter_upwards [this.eventually hδ.2.2, Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)]
      with t h1 h2
    exact (ite_eq_right (not_le.2 h2)).trans h1

variable [IsManifold 𝓘(ℂ, E) ω C]

/-- **Segments in a chart**: for a segment `[a, b]` in the target of a chart, `t ↦ φ⁻¹(a + σ(t)
(b - a))` with a smooth step `σ` is a good path from `φ⁻¹ a` to `φ⁻¹ b`. -/
theorem b3A_isGoodPath_segment (x : C) (a b : E)
    (hab : segment ℝ a b ⊆ (chartAt E x).target) :
    b3A_IsGoodPath (E := E)
      (fun t ↦ (chartAt E x).symm (a + Real.smoothTransition (3 * t - 1) • (b - a)))
      ((chartAt E x).symm a) ((chartAt E x).symm b) := by
  set σ : ℝ → ℝ := fun t ↦ Real.smoothTransition (3 * t - 1)
  have hσ : ContDiff ℝ 1 σ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hl : ContDiff ℝ 1 (fun t ↦ a + σ t • (b - a)) := contDiff_const.add (hσ.smul contDiff_const)
  have hmem : ∀ t, a + σ t • (b - a) ∈ (chartAt E x).target := fun t ↦ by
    refine hab ?_
    rw [segment_eq_image']
    exact ⟨σ t, ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, rfl⟩
  refine ⟨fun t ↦ ?_, ?_, ?_⟩
  · have h1 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E x).symm (a + σ t • (b - a)) :=
      (contMDiffOn_chart_symm (n := ω) _ (hmem t)).contMDiffAt
        ((chartAt E x).open_target.mem_nhds (hmem t))
    have h2 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (chartAt E x).symm (a + σ t • (b - a)) :=
      (b3A_contMDiffWithinAt_real h1).of_le le_top
    exact h2.comp t (hl.contMDiff t)
  · filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with t ht
    have : σ t = 0 := Real.smoothTransition.zero_of_nonpos (by
      have : t < 1 / 3 := ht
      linarith)
    show (chartAt E x).symm (a + σ t • (b - a)) = _
    rw [this, zero_smul, add_zero]
  · filter_upwards [Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with t ht
    have : σ t = 1 := Real.smoothTransition.one_of_one_le (by
      have : 2 / 3 < t := ht
      linarith)
    show (chartAt E x).symm (a + σ t • (b - a)) = _
    rw [this, one_smul, add_sub_cancel]

/-- Points joined by a good path. -/
def b3A_Joined (p q : C) : Prop := ∃ γ : ℝ → C, b3A_IsGoodPath (E := E) γ p q

/-- Every point near `q` is joined to `q` by a segment in the chart at `q`. -/
theorem b3A_joined_nhds (q : C) : ∀ᶠ q' in 𝓝 q, b3A_Joined (E := E) q q' := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (chartAt E q).open_target (chartAt E q q)
    ((chartAt E q).map_source (mem_chart_source E q))
  have hU : (chartAt E q).source ∩ chartAt E q ⁻¹' Metric.ball (chartAt E q q) r ∈ 𝓝 q :=
    (chartAt E q).continuousOn.isOpen_inter_preimage (chartAt E q).open_source
      Metric.isOpen_ball |>.mem_nhds ⟨mem_chart_source E q, Metric.mem_ball_self hr⟩
  filter_upwards [hU] with q' ⟨hq's, hq'b⟩
  have hseg : segment ℝ (chartAt E q q) (chartAt E q q') ⊆ (chartAt E q).target :=
    ((convex_ball _ _).segment_subset (Metric.mem_ball_self hr) hq'b).trans hball
  have := b3A_isGoodPath_segment q _ _ hseg
  rw [(chartAt E q).left_inv (mem_chart_source E q), (chartAt E q).left_inv hq's] at this
  exact ⟨_, this⟩

/-- **A connected Riemann surface is connected by good paths.** -/
theorem b3A_joined [ConnectedSpace C] (p q : C) : b3A_Joined (E := E) p q := by
  have hopen : IsOpen {q | b3A_Joined (E := E) p q} := by
    rw [isOpen_iff_mem_nhds]
    rintro q ⟨γ, hγ⟩
    filter_upwards [b3A_joined_nhds (E := E) q] with q' ⟨δ, hδ⟩
    exact ⟨_, hγ.trans hδ⟩
  have hclosed : IsClosed {q | b3A_Joined (E := E) p q} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro q hq
    filter_upwards [b3A_joined_nhds (E := E) q] with q' ⟨δ, hδ⟩ ⟨γ, hγ⟩
    exact hq ⟨_, hγ.trans hδ.symm⟩
  have := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨p, _, b3A_isGoodPath_const p⟩
  exact Set.eq_univ_iff_forall.1 this q

end Paths

end HodgeLean.Foundations.Program
