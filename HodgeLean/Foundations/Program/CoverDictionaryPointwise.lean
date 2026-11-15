import HodgeLean.Foundations.Program.CoverDictionaryHolo
import HodgeLean.Foundations.Program.CoverDictionaryTranslate

/-! # B6-5 stage 5d, stage four: pointwise holomorphy criteria on a fibre

At a point `x` of a fibre over a pole `t₀ = s(x)`, for a gauge `G` near `t₀`, the chart
coefficients of the r-forms `v ⬝ Y⁻¹ r ds` are bounded near `x` for every `v` exactly when
`ord_{t₀} ((G P)⁻¹ r)ᵢ ≥ mᵢ / e` (`b65g_rForm_pole_iff`), and those of the q-forms exactly when
`ord_{t₀} ((G P)ᵀ q)ᵢ ≥ (−mᵢ) / e` (`b65g_qForm_pole_iff`). Over `s = ∞` the conditions are
`ord₀ r(1/w) ≥ 2`, resp. `ord₀ q(1/w) ≥ 2` (`b65g_rForm_infty_iff`, `b65g_qForm_infty_iff`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Matrix Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

local notation "𝔼" => (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)

variable {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
  {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D)

/-- The chart coefficients of the r-forms on the punctured chart disc. -/
theorem b65g_rForm_chart (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t) (r : Fin 4 → RatFunc ℂ) (v : Fin 4 → ℂ) :
    (fun z ↦ b65g_rForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) r v
        ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
          mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩) =ᶠ[𝓝[≠]
        (extChartAt 𝓘(ℂ, ℂ) x x)]
      fun z ↦ (v ⬝ᵥ ((b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z))⁻¹ *ᵥ
          fun j ↦ b65q_eval (r j) (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
            ((extChartAt 𝓘(ℂ, ℂ) x).symm z)))) *
        deriv (fun w ↦ b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
          ((extChartAt 𝓘(ℂ, ℂ) x).symm w)) z := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero ha hb
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  filter_upwards [b65g_chart_punctured_good D t hab' hba (b65p_poles p θ) x] with z ⟨hz, hg⟩
  obtain ⟨-, -, hd⟩ := b65g_chart_ode S θ hθ t ht x z hz hg
  simp only [b65g_rForm]
  rw [hd.deriv]

/-- The chart coefficients of the q-forms on the punctured chart disc. -/
theorem b65g_qForm_chart (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t) (q : Fin 4 → RatFunc ℂ) (v : Fin 4 → ℂ) :
    (fun z ↦ b65g_qForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) q v
        ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
          mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩) =ᶠ[𝓝[≠]
        (extChartAt 𝓘(ℂ, ℂ) x x)]
      fun z ↦ (v ⬝ᵥ ((b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z))ᵀ *ᵥ
          fun j ↦ b65q_eval (q j) (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
            ((extChartAt 𝓘(ℂ, ℂ) x).symm z)))) *
        deriv (fun w ↦ b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
          ((extChartAt 𝓘(ℂ, ℂ) x).symm w)) z := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero ha hb
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  filter_upwards [b65g_chart_punctured_good D t hab' hba (b65p_poles p θ) x] with z ⟨hz, hg⟩
  obtain ⟨-, -, hd⟩ := b65g_chart_ode S θ hθ t ht x z hz hg
  simp only [b65g_qForm]
  rw [hd.deriv]

/-- The matrix of the local form at a pole. -/
theorem b65g_mat_local (G : 𝔼) (P : 𝔼) (dκ : Fin 4 → ℂ) (K : 𝔼) :
    b65q_mat (G * P * b65r_operator (diagonal dκ) * K) =
      (b65q_mat G * b65q_mat P) * diagonal dκ * b65q_mat K := by
  rw [caf_mat_mul, caf_mat_mul, caf_mat_mul, b65q_mat_operator]

/-- Entries of the gauge matrix `G P` are analytic. -/
theorem b65g_gauge_mat_analytic (G : ℂ → 𝔼) (P : 𝔼) (t₀ : ℂ)
    (hGa : ∀ i j, AnalyticAt ℂ (fun σ ↦ b65q_mat (G σ) i j) t₀) (i j : Fin 4) :
    AnalyticAt ℂ (fun σ ↦ (b65q_mat (G σ) * b65q_mat P) i j) t₀ :=
  caf_matrix_mul_analyticAt _ (fun _ ↦ b65q_mat P) t₀ hGa (fun _ _ ↦ analyticAt_const) i j

/-- **The pointwise criterion for r-forms at a pole.** -/
theorem b65g_rForm_pole_iff (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : b63d_projection (b65z_centre p) D.C D.atlas.f (b6t_polydisc (b65z_centre p))
      (Subset.refl _) t x ≠ ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) : ℂ) :
        OnePoint ℂ))
    (G : ℂ → 𝔼) (Λ P : 𝔼) (hP : IsUnit P) (d : Fin 4 → ℂ)
    (hΛ : Λ * P = P * b65r_operator (diagonal d))
    (hGa : ∀ i j, AnalyticAt ℂ (fun σ ↦ b65q_mat (G σ) i j)
      (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x))
    (hGu : ∀ᶠ σ in 𝓝 (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x),
      IsUnit (G σ))
    (hG : ∀ᶠ σ in 𝓝[≠] (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x),
      HasDerivAt G (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ) σ * G σ -
        (σ - b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x)⁻¹ • (G σ * Λ)) σ)
    (r : Fin 4 → RatFunc ℂ) :
    ∃ e : ℕ, 0 < e ∧ ∃ m : Fin 4 → ℤ, (∀ i, (e : ℂ) * d i = m i) ∧
      ((∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
        ‖b65g_rForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) r v
          ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B) ↔
        ∀ i, ((m i / e : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
          (fun σ ↦ ((b65q_mat (G σ) * b65q_mat P)⁻¹ *ᵥ fun j ↦ b65q_eval (r j) σ) i)
          (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x)) := by
  obtain ⟨e, he, l, hl, hl0, hs, m, hm, K, hK, hY⟩ :=
    b65g_local_pole S θ hθ t ht x hx G Λ P hP d hΛ hGu hG
  refine ⟨e, he, m, hm, ?_⟩
  have hMd : (b65q_mat (G (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x)) *
      b65q_mat P).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (b65g_mat_det_ne hGu.self_of_nhds).ne_zero (b65g_mat_det_ne hP).ne_zero
  have hYm : ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
      b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z) =
        (b65q_mat (G (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
          ((extChartAt 𝓘(ℂ, ℂ) x).symm z))) * b65q_mat P) *
          diagonal (fun i ↦ ((z - extChartAt 𝓘(ℂ, ℂ) x x) * l z) ^ m i) * b65q_mat K := by
    filter_upwards [hY] with z hz
    simp only [b65g_Y]
    rw [hz, b65g_mat_local]
  refine (forall_congr' fun v ↦ caf_bdd_congr (b65g_rForm_chart S θ hθ t ht x r v)).trans ?_
  exact caf_pole_rForm_iff (fun z ↦ b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) l _ _ e he hl hl0 hs
    (fun σ ↦ b65q_mat (G σ) * b65q_mat P) (b65g_gauge_mat_analytic G P _ hGa) hMd m _ (b65g_mat_det_ne hK) (fun z ↦ b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) hYm
    (fun σ j ↦ b65q_eval (r j) σ) (fun j ↦ caf_eval_meromorphicAt (r j) _)

/-- **The pointwise criterion for q-forms at a pole.** -/
theorem b65g_qForm_pole_iff (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : b63d_projection (b65z_centre p) D.C D.atlas.f (b6t_polydisc (b65z_centre p))
      (Subset.refl _) t x ≠ ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) : ℂ) :
        OnePoint ℂ))
    (G : ℂ → 𝔼) (Λ P : 𝔼) (hP : IsUnit P) (d : Fin 4 → ℂ)
    (hΛ : Λ * P = P * b65r_operator (diagonal d))
    (hGa : ∀ i j, AnalyticAt ℂ (fun σ ↦ b65q_mat (G σ) i j)
      (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x))
    (hGu : ∀ᶠ σ in 𝓝 (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x),
      IsUnit (G σ))
    (hG : ∀ᶠ σ in 𝓝[≠] (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x),
      HasDerivAt G (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ) σ * G σ -
        (σ - b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x)⁻¹ • (G σ * Λ)) σ)
    (q : Fin 4 → RatFunc ℂ) :
    ∃ e : ℕ, 0 < e ∧ ∃ m : Fin 4 → ℤ, (∀ i, (e : ℂ) * d i = m i) ∧
      ((∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
        ‖b65g_qForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) q v
          ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B) ↔
        ∀ i, (((-m i) / e : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
          (fun σ ↦ ((b65q_mat (G σ) * b65q_mat P)ᵀ *ᵥ fun j ↦ b65q_eval (q j) σ) i)
          (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x)) := by
  obtain ⟨e, he, l, hl, hl0, hs, m, hm, K, hK, hY⟩ :=
    b65g_local_pole S θ hθ t ht x hx G Λ P hP d hΛ hGu hG
  refine ⟨e, he, m, hm, ?_⟩
  have hYm : ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
      b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z) =
        (b65q_mat (G (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
          ((extChartAt 𝓘(ℂ, ℂ) x).symm z))) * b65q_mat P) *
          diagonal (fun i ↦ ((z - extChartAt 𝓘(ℂ, ℂ) x x) * l z) ^ m i) * b65q_mat K := by
    filter_upwards [hY] with z hz
    simp only [b65g_Y]
    rw [hz, b65g_mat_local]
  refine (forall_congr' fun v ↦ caf_bdd_congr (b65g_qForm_chart S θ hθ t ht x q v)).trans ?_
  exact caf_pole_qForm_iff (fun z ↦ b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) l _ _ e he hl hl0 hs
    (fun σ ↦ b65q_mat (G σ) * b65q_mat P) (b65g_gauge_mat_analytic G P _ hGa) m _ (b65g_mat_det_ne hK) (fun z ↦ b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) hYm
    (fun σ j ↦ b65q_eval (q j) σ) (fun j ↦ caf_eval_meromorphicAt (q j) _)

/-- The matrix of the local form over infinity. -/
theorem b65g_infty_mat (Φ : ℂ → 𝔼) (z₀ : ℂ) (hΦ : AnalyticAt ℂ Φ z₀) (hΦ1 : Φ z₀ = 1) :
    (∀ i j, AnalyticAt ℂ (fun z ↦ b65q_mat (Φ z) i j) z₀) ∧ (b65q_mat (Φ z₀)).det ≠ 0 := by
  refine ⟨fun i j ↦ ?_, ?_⟩
  · refine (((b65q_entryCLM i j).analyticAt _).comp hΦ).congr (Eventually.of_forall fun z ↦ ?_)
    simp [b65q_entryCLM_apply]
  · rw [hΦ1, show b65q_mat 1 = 1 from map_one b65q_matAlg, det_one]
    exact one_ne_zero

/-- **The pointwise criterion for r-forms over `s = ∞`.** -/
theorem b65g_rForm_infty_iff (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : b63d_projection (b65z_centre p) D.C D.atlas.f (b6t_polydisc (b65z_centre p))
      (Subset.refl _) t x = ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) : ℂ) :
        OnePoint ℂ)) (r : Fin 4 → RatFunc ℂ) :
    (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
        ‖b65g_rForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) r v
          ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B) ↔
      ∀ j, r j = 0 ∨ (r j).intDegree ≤ -2 := by
  obtain ⟨e, he, l, hl, hl0, hs, Φ, hΦ, hΦ1, K, hK, hY⟩ := b65g_local_infty S θ hθ t ht x hx
  obtain ⟨hΦa, hΦd⟩ := b65g_infty_mat Φ _ hΦ hΦ1
  have hYm : ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
      b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z) = b65q_mat (Φ z) * b65q_mat K := by
    filter_upwards [hY] with z hz
    simp only [b65g_Y]
    rw [hz, caf_mat_mul]
  refine (forall_congr' fun v ↦ caf_bdd_congr (b65g_rForm_chart S θ hθ t ht x r v)).trans ?_
  refine (caf_infty_rForm_iff (fun z ↦ b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) l _ e he hl hl0 hs (fun z ↦ b65q_mat (Φ z)) hΦa hΦd _
    (b65g_mat_det_ne hK) (fun z ↦ b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) hYm (fun σ j ↦ b65q_eval (r j) σ)
    (fun j ↦ (caf_order_ratFunc_inv (r j)).1)).trans ?_
  exact forall_congr' fun j ↦ (caf_order_ratFunc_inv (r j)).2

/-- **The pointwise criterion for q-forms over `s = ∞`.** -/
theorem b65g_qForm_infty_iff (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : b63d_projection (b65z_centre p) D.C D.atlas.f (b6t_polydisc (b65z_centre p))
      (Subset.refl _) t x = ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) : ℂ) :
        OnePoint ℂ)) (q : Fin 4 → RatFunc ℂ) :
    (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
        ‖b65g_qForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) q v
          ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B) ↔
      ∀ j, q j = 0 ∨ (q j).intDegree ≤ -2 := by
  obtain ⟨e, he, l, hl, hl0, hs, Φ, hΦ, hΦ1, K, hK, hY⟩ := b65g_local_infty S θ hθ t ht x hx
  obtain ⟨hΦa, hΦd⟩ := b65g_infty_mat Φ _ hΦ hΦ1
  have hYm : ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
      b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z) = b65q_mat (Φ z) * b65q_mat K := by
    filter_upwards [hY] with z hz
    simp only [b65g_Y]
    rw [hz, caf_mat_mul]
  refine (forall_congr' fun v ↦ caf_bdd_congr (b65g_qForm_chart S θ hθ t ht x q v)).trans ?_
  refine (caf_infty_qForm_iff (fun z ↦ b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) l _ e he hl hl0 hs (fun z ↦ b65q_mat (Φ z)) hΦa hΦd _
    (b65g_mat_det_ne hK) (fun z ↦ b65g_Y S θ t ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) hYm (fun σ j ↦ b65q_eval (q j) σ)
    (fun j ↦ (caf_order_ratFunc_inv (q j)).1)).trans ?_
  exact forall_congr' fun j ↦ (caf_order_ratFunc_inv (q j)).2

end HodgeLean.Foundations.Program
