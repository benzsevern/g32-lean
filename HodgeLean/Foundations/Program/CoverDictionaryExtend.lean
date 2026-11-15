import HodgeLean.Foundations.Program.CoverDictionaryPointwise

/-! # B6-5 stage 5d, stage four: the extension equivalences

For a record `S` of pulled-back solutions, a parameter `θ` in its disc and normal-form gauges `H`
at the fixed poles (with the gauges `G = b65q_basis · H` of the record), a rational vector `r`
regular off the poles has r-forms `v ⬝ Y⁻¹ r ds` that extend to holomorphic forms for every `v`
exactly when `r ∈ b65q_rSpace` (`b65g_rForm_extends_iff`); likewise for q-forms and `b65q_qSpace`
(`b65g_qForm_extends_iff`).
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

section Fibre

variable {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
  (t : b6t_polydisc c) {a b : ℂ}

/-- **Every value of `s` is taken** over a finite `s`. -/
theorem b65g_exists_over (hab : a * b ≠ 0) (hba : b - a ≠ 0) (s : ℂ) :
    ∃ x : b65z_fibre c D.C t, b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x
      ≠ ((b / (b - a) : ℂ) : OnePoint ℂ) ∧ b65g_sFun D t a b x = s := by
  by_cases hs : s = 0
  · obtain ⟨x, hx⟩ := D.hsurj t OnePoint.infty
    refine ⟨x, by rw [hx]; exact OnePoint.infty_ne_coe _, ?_⟩
    simp only [b65g_sFun, hx, hs]
    rfl
  · obtain ⟨x, hx⟩ := D.hsurj t ((b65s_normalize a b s : ℂ) : OnePoint ℂ)
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    have hval : b - b65s_normalize a b s * (b - a) = a * b / s := by
      simp only [b65s_normalize]
      field_simp
      ring
    have hsC : b65g_sCoord a b ((b65s_normalize a b s : ℂ) : OnePoint ℂ) = s := by
      change a * b / (b - b65s_normalize a b s * (b - a)) = s
      rw [hval]
      field_simp
    refine ⟨x, ?_, ?_⟩
    · rw [hx]
      intro h
      have h' : b65s_normalize a b s = b / (b - a) := OnePoint.coe_injective h
      have : b - b65s_normalize a b s * (b - a) = 0 := by rw [h', div_mul_cancel₀ _ hba, sub_self]
      rw [hval] at this
      exact div_ne_zero hab hs this
    · simp only [b65g_sFun, hx, hsC]

/-- A non-regular point over a finite `s` lies over a pole. -/
theorem b65g_nongood_pole (hba : b - a ≠ 0) (poles : Fin 4 ⊕ Fin 12 → ℂ)
    (h0 : poles (Sum.inl 0) = 0) (x : b65z_fibre c D.C t) (hx : x ∉ b65g_good D t a b poles)
    (hfin : b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x ≠
      ((b / (b - a) : ℂ) : OnePoint ℂ)) :
    ∃ q, poles q = b65g_sFun D t a b x := by
  cases hpx : b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x with
  | infty =>
    refine ⟨Sum.inl 0, ?_⟩
    simp only [b65g_sFun, hpx, h0]
    rfl
  | coe z =>
    have hz : b - z * (b - a) ≠ 0 := by
      intro h
      apply hfin
      rw [hpx]
      congr 1
      field_simp
      linear_combination -h
    by_contra hne
    push Not at hne
    refine hx ⟨z, hpx, hz, ?_⟩
    rintro ⟨q, hq⟩
    exact hne q (by simp only [b65g_sFun, hpx, hq])

end Fibre

section General

variable {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]

/-- **The chart coefficient of a holomorphic form is bounded** near the chart value. -/
theorem caf_holForm_chart_bdd (ω' : TangentBundle 𝓘(ℂ, ℂ) M → ℂ) (hω : ω' ∈ b3_HolForm ℂ M)
    (x : M) : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
      ‖ω' ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B := by
  have h1 : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : ℂ ↦ ω' ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩)
      (extChartAt 𝓘(ℂ, ℂ) x x) :=
    (hω.1 _).comp _ (caf_contMDiffAt_chart_field x _ (mem_extChartAt_target x))
  have hc : ContinuousAt (fun z : ℂ ↦ ‖ω' ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖)
      (extChartAt 𝓘(ℂ, ℂ) x x) := h1.continuousAt.norm
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) x x),
      ‖ω' ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B :=
    ⟨_, (hc.eventually (gt_mem_nhds (lt_add_one _))).mono fun z hz ↦ hz.le⟩
  exact ⟨B, nhdsWithin_le_nhds hB⟩

end General

variable {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
  {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D)

/-- A function agreeing with a holomorphic form on the regular locus has bounded chart
coefficients at every point. -/
theorem b65g_agree_bdd (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p))
    (f ω' : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)
    (hω : ω' ∈ b3_HolForm ℂ (b65z_fibre (b65z_centre p) D.C t))
    (he : ∀ u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t),
      u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
        ω' u = f u)
    (x : b65z_fibre (b65z_centre p) D.C t) :
    ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
      ‖f ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero ha hb
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  obtain ⟨B, hB⟩ := caf_holForm_chart_bdd ω' hω x
  refine ⟨B, ?_⟩
  have hgood := b65g_chart_punctured_good D t hab' hba (b65p_poles p θ) x
  filter_upwards [hB, hgood] with z hz hg
  have := he ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩ hg.2
  rw [← this]
  exact hz


/-- Fibrewise linearity of the r-forms. -/
theorem b65g_rForm_linear (t : b6t_polydisc (b65z_centre p)) (a b : ℂ)
    (Y : b65z_fibre (b65z_centre p) D.C t → Matrix (Fin 4) (Fin 4) ℂ) (r : Fin 4 → RatFunc ℂ)
    (v : Fin 4 → ℂ) (x : b65z_fibre (b65z_centre p) D.C t) (c : ℂ)
    (w₁ w₂ : TangentSpace 𝓘(ℂ, ℂ) x) :
    b65g_rForm D t a b Y r v ⟨x, c • w₁ + w₂⟩ =
      c * b65g_rForm D t a b Y r v ⟨x, w₁⟩ + b65g_rForm D t a b Y r v ⟨x, w₂⟩ := by
  simp only [b65g_rForm, b65g_ds, map_add, map_smul]
  change _ * (c * _ + _) = _
  have key : ∀ X A₁ A₂ : ℂ, X * (c * A₁ + A₂) = c * (X * A₁) + X * A₂ := fun _ _ _ ↦ by ring
  exact key _ _ _

/-- Fibrewise linearity of the q-forms. -/
theorem b65g_qForm_linear (t : b6t_polydisc (b65z_centre p)) (a b : ℂ)
    (Y : b65z_fibre (b65z_centre p) D.C t → Matrix (Fin 4) (Fin 4) ℂ) (q : Fin 4 → RatFunc ℂ)
    (v : Fin 4 → ℂ) (x : b65z_fibre (b65z_centre p) D.C t) (c : ℂ)
    (w₁ w₂ : TangentSpace 𝓘(ℂ, ℂ) x) :
    b65g_qForm D t a b Y q v ⟨x, c • w₁ + w₂⟩ =
      c * b65g_qForm D t a b Y q v ⟨x, w₁⟩ + b65g_qForm D t a b Y q v ⟨x, w₂⟩ := by
  simp only [b65g_qForm, b65g_ds, map_add, map_smul]
  change _ * (c * _ + _) = _
  have key : ∀ X A₁ A₂ : ℂ, X * (c * A₁ + A₂) = c * (X * A₁) + X * A₂ := fun _ _ _ ↦ by ring
  exact key _ _ _

/-- Entries of the fixed-pole gauge matrices are analytic. -/
theorem b65g_fixed_mat_analytic (θ : ℂ) (k : Fin 4) (H : ℂ → Matrix (Fin 4) (Fin 4) ℂ)
    (G : ℂ → 𝔼) (hGm : ∀ s, b65q_mat (G s) = b65q_basis O.residue θ k * H s)
    (hHa : ∀ i j, AnalyticAt ℂ (fun s ↦ H s i j) (b65p_fixedPole k)) (i j : Fin 4) :
    AnalyticAt ℂ (fun σ ↦ b65q_mat (G σ) i j) (b65p_fixedPole k) := by
  simp only [hGm]
  exact caf_matrix_mul_analyticAt (fun _ ↦ b65q_basis O.residue θ k) H _
    (fun _ _ ↦ analyticAt_const) hHa i j

/-- The data of the moving-pole gauge used by the criteria. -/
theorem b65g_moving_data (θ : ℂ) (hθO : θ ∈ ball (0 : ℂ) O.radius) (j : Fin 12) :
    ∃ q : ℚ, (q = 1 / 3 ∨ q = 2 / 3) ∧ ∃ Pm : Matrix (Fin 4) (Fin 4) ℂ, IsUnit Pm.det ∧
      b65q_res O.residue θ (Sum.inr j) * Pm = Pm * diagonal ![0, 0, 0, (q : ℂ)] ∧
      O.residue θ (Sum.inr j) * b65r_operator Pm =
        b65r_operator Pm * b65r_operator (diagonal ![0, 0, 0, (q : ℂ)]) ∧
      ∃ G : ℂ → 𝔼, (∀ i k, AnalyticAt ℂ (fun σ ↦ b65q_mat (G σ) i k) (b65p_poles p θ (Sum.inr j))) ∧
        b65q_mat (G (b65p_poles p θ (Sum.inr j))) = 1 ∧
        (∀ᶠ σ in 𝓝 (b65p_poles p θ (Sum.inr j)), IsUnit (G σ)) ∧
        ∀ᶠ σ in 𝓝[≠] (b65p_poles p θ (Sum.inr j)), HasDerivAt G
          (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ) σ * G σ -
            (σ - b65p_poles p θ (Sum.inr j))⁻¹ • (G σ * O.residue θ (Sum.inr j))) σ := by
  obtain ⟨q, hq, hspec⟩ := caf_moving_spectrum O j
  obtain ⟨-, ⟨Pm, hPmu, hPme⟩, -⟩ := hspec θ hθO
  obtain ⟨G, hGa, hG1, hGu, hGd⟩ := b65g_moving_gauge O θ hθO j
  refine ⟨q, hq, Pm, (Matrix.isUnit_iff_isUnit_det _).mp hPmu, hPme, ?_, G, fun i k ↦ ?_, ?_,
    hGu, hGd⟩
  · apply b65q_mat_injective
    rw [caf_mat_mul, caf_mat_mul, b65q_mat_operator, b65q_mat_operator]
    exact hPme
  · refine (((b65q_entryCLM i k).analyticAt _).comp hGa).congr (Eventually.of_forall fun z ↦ ?_)
    simp [b65q_entryCLM_apply]
  · rw [hG1]; exact map_one b65q_matAlg

/-- **The r-forms extend exactly for the r-space.** -/
theorem b65g_rForm_extends_iff (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (H : Fin 4 → ℂ → Matrix (Fin 4) (Fin 4) ℂ) (G : Fin 4 → ℂ → 𝔼)
    (hGm : ∀ k s, b65q_mat (G k s) = b65q_basis O.residue θ k * H k s)
    (hHa : ∀ k i j, AnalyticAt ℂ (fun s ↦ H k s i j) (b65p_fixedPole k))
    (hGu : ∀ k, ∀ᶠ σ in 𝓝 (b65p_fixedPole k), IsUnit (G k σ))
    (hGd : ∀ k, ∀ᶠ σ in 𝓝[≠] (b65p_fixedPole k), HasDerivAt (G k)
      (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ) σ * G k σ -
        (σ - b65p_fixedPole k)⁻¹ • (G k σ * b65p_exponent k)) σ)
    (r : Fin 4 → RatFunc ℂ)
    (hr : ∀ i s, (r i).denom.eval s = 0 → s ∈ Set.range (b65p_poles p θ)) :
    (∀ v : Fin 4 → ℂ, ∃ ω' ∈ b3_HolForm ℂ (b65z_fibre (b65z_centre p) D.C t),
      ∀ u, u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
        ω' u = b65g_rForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) r v u) ↔
      r ∈ b65q_rSpace (b65p_poles p θ) (b65q_basis O.residue θ) H := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero ha hb
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  -- the pointwise criteria
  have cfix : ∀ (k : Fin 4) (x : b65z_fibre (b65z_centre p) D.C t)
      (hx : b63d_projection (b65z_centre p) D.C D.atlas.f (b6t_polydisc (b65z_centre p))
        (Subset.refl _) t x ≠ ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) :
          ℂ) : OnePoint ℂ))
      (hxs : b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x = b65p_fixedPole k),
      (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
        ‖b65g_rForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) r v
          ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B) ↔
        ∀ j, ((⌊(b65p_exponents k j).re⌋ : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
          (fun s ↦ ((b65q_basis O.residue θ k * H k s)⁻¹ *ᵥ fun i ↦ b65q_eval (r i) s) j)
          (b65p_fixedPole k) := by
    intro k x hx hxs
    obtain ⟨e, he, m, hm, hiff⟩ := b65g_rForm_pole_iff S θ hθ t ht x hx (G k) (b65p_exponent k) 1
      isUnit_one (b65p_exponents k) (by rw [mul_one, one_mul]; rfl)
      (by rw [hxs]; exact b65g_fixed_mat_analytic θ k (H k) (G k) (hGm k) (hHa k))
      (by rw [hxs]; exact hGu k) (by rw [hxs]; exact hGd k) r
    rw [hiff, hxs]
    refine forall_congr' fun j ↦ ?_
    rw [(caf_floor_div e he _ (m j) (hm j)).1]
    simp only [hGm, show b65q_mat (1 : 𝔼) = 1 from map_one b65q_matAlg, mul_one]
  have cmov : ∀ (j : Fin 12) (x : b65z_fibre (b65z_centre p) D.C t)
      (hx : b63d_projection (b65z_centre p) D.C D.atlas.f (b6t_polydisc (b65z_centre p))
        (Subset.refl _) t x ≠ ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) :
          ℂ) : OnePoint ℂ))
      (hxs : b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x =
        b65p_poles p θ (Sum.inr j)),
      (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
        ‖b65g_rForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) r v
          ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B) ↔
        ∀ i, (r i).denom.eval (b65p_poles p θ (Sum.inr j)) ≠ 0 := by
    intro j x hx hxs
    obtain ⟨q, hq, Pm, hPm, -, hΛ, Gm, hGma, hGm1, hGmu, hGmd⟩ := b65g_moving_data θ hθO j
    obtain ⟨e, he, m, hm, hiff⟩ := b65g_rForm_pole_iff S θ hθ t ht x hx Gm
      (O.residue θ (Sum.inr j)) (b65r_operator Pm)
      (caf_operator_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hPm)) _ hΛ
      (by rw [hxs]; exact hGma) (by rw [hxs]; exact hGmu) (by rw [hxs]; exact hGmd) r
    rw [hiff, hxs]
    have hq0 := (caf_moving_quotients e he q hq m hm).1
    simp only [hq0, WithTop.coe_zero, b65q_mat_operator]
    have hMd : (b65q_mat (Gm (b65p_poles p θ (Sum.inr j))) * Pm).det ≠ 0 := by
      rw [hGm1, one_mul]; exact hPm.ne_zero
    rw [caf_moving_r_iff (fun σ ↦ b65q_mat (Gm σ) * Pm) _
      (caf_matrix_mul_analyticAt _ (fun _ ↦ Pm) _ hGma (fun _ _ ↦ analyticAt_const)) hMd
      (fun σ i ↦ b65q_eval (r i) σ) (fun i ↦ caf_eval_meromorphicAt (r i) _)]
    exact forall_congr' fun i ↦ caf_order_ratFunc_nonneg_iff (r i) _
  have cinf := fun x hx ↦ b65g_rForm_infty_iff S θ hθ t ht x hx r
  constructor
  · intro hω
    have hbd : ∀ (x : b65z_fibre (b65z_centre p) D.C t) (v : Fin 4 → ℂ), ∃ B : ℝ,
        ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
          ‖b65g_rForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) r v
            ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
              mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B := by
      intro x v
      obtain ⟨ω', hω', he⟩ := hω v
      exact b65g_agree_bdd S θ hθ t _ ω' hω' he x
    refine ⟨hr, fun j i ↦ ?_, fun k j ↦ ?_, ?_⟩
    · obtain ⟨x, hx, hxs⟩ := b65g_exists_over D t hab' hba (b65p_poles p θ (Sum.inr j))
      exact (cmov j x hx hxs).mp (hbd x) i
    · obtain ⟨x, hx, hxs⟩ := b65g_exists_over D t hab' hba (b65p_fixedPole k)
      exact (cfix k x hx hxs).mp (hbd x) j
    · obtain ⟨x, hx⟩ := D.hsurj t ((b65p_moving p θ 11 /
        (b65p_moving p θ 11 - b65p_moving p θ 10) : ℂ) : OnePoint ℂ)
      exact (cinf x hx).mp (hbd x)
  · rintro ⟨-, hr2, hr3, hr4⟩ v
    have hF := b65g_good_compl_finite D t hab' hba (b65p_poles p θ)
    have hbdd : ∀ x ∈ (b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11)
        (b65p_poles p θ))ᶜ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
          ‖b65g_rForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) r v
            ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
              mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B := by
      intro x hx
      by_cases hxi : b63d_projection (b65z_centre p) D.C D.atlas.f (b6t_polydisc (b65z_centre p))
          (Subset.refl _) t x = ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) :
            ℂ) : OnePoint ℂ)
      · exact (cinf x hxi).mpr hr4 v
      · obtain ⟨q, hq⟩ := b65g_nongood_pole D t hba (b65p_poles p θ) rfl x hx hxi
        cases q with
        | inl k => exact (cfix k x hxi hq.symm).mpr (hr3 k) v
        | inr j => exact (cmov j x hxi hq.symm).mpr (hr2 j) v
    obtain ⟨ω', hω', hωe⟩ := caf_holForm_extend _
      (b65g_rForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) r v) _ hF
      (fun u hu ↦ b65g_rForm_contMDiffAt S θ hθ t ht r hr v u (not_not.mp hu))
      (fun x _ c w₁ w₂ ↦ b65g_rForm_linear t _ _ _ r v x c w₁ w₂) hbdd
    exact ⟨ω', hω', fun u hu ↦ hωe u (not_not.mpr hu)⟩


/-- **The q-forms extend exactly for the q-space.** -/
theorem b65g_qForm_extends_iff (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (H : Fin 4 → ℂ → Matrix (Fin 4) (Fin 4) ℂ) (G : Fin 4 → ℂ → 𝔼)
    (hGm : ∀ k s, b65q_mat (G k s) = b65q_basis O.residue θ k * H k s)
    (hHa : ∀ k i j, AnalyticAt ℂ (fun s ↦ H k s i j) (b65p_fixedPole k))
    (hGu : ∀ k, ∀ᶠ σ in 𝓝 (b65p_fixedPole k), IsUnit (G k σ))
    (hGd : ∀ k, ∀ᶠ σ in 𝓝[≠] (b65p_fixedPole k), HasDerivAt (G k)
      (b65p_coefficient (Fin 4 → ℂ) (b65p_poles p θ) (O.residue θ) σ * G k σ -
        (σ - b65p_fixedPole k)⁻¹ • (G k σ * b65p_exponent k)) σ)
    (q : Fin 4 → RatFunc ℂ)
    (hq : ∀ i s, (q i).denom.eval s = 0 → s ∈ Set.range (b65p_poles p θ)) :
    (∀ v : Fin 4 → ℂ, ∃ ω' ∈ b3_HolForm ℂ (b65z_fibre (b65z_centre p) D.C t),
      ∀ u, u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
        ω' u = b65g_qForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) q v u) ↔
      q ∈ b65q_qSpace (b65p_poles p θ) (b65q_res O.residue θ) (b65q_basis O.residue θ) H := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero ha hb
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have cfix : ∀ (k : Fin 4) (x : b65z_fibre (b65z_centre p) D.C t)
      (hx : b63d_projection (b65z_centre p) D.C D.atlas.f (b6t_polydisc (b65z_centre p))
        (Subset.refl _) t x ≠ ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) :
          ℂ) : OnePoint ℂ))
      (hxs : b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x = b65p_fixedPole k),
      (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
        ‖b65g_qForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) q v
          ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B) ↔
        ∀ j, ((⌊(-b65p_exponents k j).re⌋ : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
          (fun s ↦ ((b65q_basis O.residue θ k * H k s)ᵀ *ᵥ fun i ↦ b65q_eval (q i) s) j)
          (b65p_fixedPole k) := by
    intro k x hx hxs
    obtain ⟨e, he, m, hm, hiff⟩ := b65g_qForm_pole_iff S θ hθ t ht x hx (G k) (b65p_exponent k) 1
      isUnit_one (b65p_exponents k) (by rw [mul_one, one_mul]; rfl)
      (by rw [hxs]; exact b65g_fixed_mat_analytic θ k (H k) (G k) (hGm k) (hHa k))
      (by rw [hxs]; exact hGu k) (by rw [hxs]; exact hGd k) q
    rw [hiff, hxs]
    refine forall_congr' fun j ↦ ?_
    rw [(caf_floor_div e he _ (m j) (hm j)).2]
    simp only [hGm, show b65q_mat (1 : 𝔼) = 1 from map_one b65q_matAlg, mul_one]
  have cmov : ∀ (j : Fin 12) (x : b65z_fibre (b65z_centre p) D.C t)
      (hx : b63d_projection (b65z_centre p) D.C D.atlas.f (b6t_polydisc (b65z_centre p))
        (Subset.refl _) t x ≠ ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) :
          ℂ) : OnePoint ℂ))
      (hxs : b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x =
        b65p_poles p θ (Sum.inr j)),
      (∀ v : Fin 4 → ℂ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
        ‖b65g_qForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) q v
          ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B) ↔
        (∀ i, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun s ↦ b65q_eval (q i) s)
          (b65p_poles p θ (Sum.inr j))) ∧
        ∀ v, b65q_res O.residue θ (Sum.inr j) *ᵥ v = 0 → (0 : WithTop ℤ) ≤
          meromorphicOrderAt (fun s ↦ v ⬝ᵥ fun i ↦ b65q_eval (q i) s)
            (b65p_poles p θ (Sum.inr j)) := by
    intro j x hx hxs
    obtain ⟨qq, hqq, Pm, hPm, hPme, hΛ, Gm, hGma, hGm1, hGmu, hGmd⟩ := b65g_moving_data θ hθO j
    obtain ⟨e, he, m, hm, hiff⟩ := b65g_qForm_pole_iff S θ hθ t ht x hx Gm
      (O.residue θ (Sum.inr j)) (b65r_operator Pm)
      (caf_operator_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hPm)) _ hΛ
      (by rw [hxs]; exact hGma) (by rw [hxs]; exact hGmu) (by rw [hxs]; exact hGmd) q
    rw [hiff, hxs]
    have hq0 := (caf_moving_quotients e he qq hqq m hm).2
    simp only [hq0, b65q_mat_operator]
    have hqne : ((qq : ℚ) : ℂ) ≠ 0 := by
      rcases hqq with rfl | rfl <;> norm_num
    exact caf_moving_q_iff (fun σ ↦ b65q_mat (Gm σ)) _ hGma hGm1 Pm _ hPm _ hqne hPme
      (fun σ i ↦ b65q_eval (q i) σ) (fun i ↦ caf_eval_meromorphicAt (q i) _)
  have cinf := fun x hx ↦ b65g_qForm_infty_iff S θ hθ t ht x hx q
  constructor
  · intro hω
    have hbd : ∀ (x : b65z_fibre (b65z_centre p) D.C t) (v : Fin 4 → ℂ), ∃ B : ℝ,
        ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
          ‖b65g_qForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) q v
            ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
              mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B := by
      intro x v
      obtain ⟨ω', hω', he⟩ := hω v
      exact b65g_agree_bdd S θ hθ t _ ω' hω' he x
    refine ⟨hq, fun j i ↦ ?_, fun j v hv ↦ ?_, fun k j ↦ ?_, ?_⟩
    · obtain ⟨x, hx, hxs⟩ := b65g_exists_over D t hab' hba (b65p_poles p θ (Sum.inr j))
      exact ((cmov j x hx hxs).mp (hbd x)).1 i
    · obtain ⟨x, hx, hxs⟩ := b65g_exists_over D t hab' hba (b65p_poles p θ (Sum.inr j))
      exact ((cmov j x hx hxs).mp (hbd x)).2 v hv
    · obtain ⟨x, hx, hxs⟩ := b65g_exists_over D t hab' hba (b65p_fixedPole k)
      exact (cfix k x hx hxs).mp (hbd x) j
    · obtain ⟨x, hx⟩ := D.hsurj t ((b65p_moving p θ 11 /
        (b65p_moving p θ 11 - b65p_moving p θ 10) : ℂ) : OnePoint ℂ)
      exact (cinf x hx).mp (hbd x)
  · rintro ⟨-, hq2, hq3, hq4, hq5⟩ v
    have hF := b65g_good_compl_finite D t hab' hba (b65p_poles p θ)
    have hbdd : ∀ x ∈ (b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11)
        (b65p_poles p θ))ᶜ, ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x),
          ‖b65g_qForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) q v
            ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
              mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩‖ ≤ B := by
      intro x hx
      by_cases hxi : b63d_projection (b65z_centre p) D.C D.atlas.f (b6t_polydisc (b65z_centre p))
          (Subset.refl _) t x = ((b65p_moving p θ 11 / (b65p_moving p θ 11 - b65p_moving p θ 10) :
            ℂ) : OnePoint ℂ)
      · exact (cinf x hxi).mpr hq5 v
      · obtain ⟨r, hr⟩ := b65g_nongood_pole D t hba (b65p_poles p θ) rfl x hx hxi
        cases r with
        | inl k => exact (cfix k x hxi hr.symm).mpr (hq4 k) v
        | inr j => exact (cmov j x hxi hr.symm).mpr ⟨hq2 j, hq3 j⟩ v
    obtain ⟨ω', hω', hωe⟩ := caf_holForm_extend _
      (b65g_qForm D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65g_Y S θ t) q v) _ hF
      (fun u hu ↦ b65g_qForm_contMDiffAt S θ hθ t ht q hq v u (not_not.mp hu))
      (fun x _ c w₁ w₂ ↦ b65g_qForm_linear t _ _ _ q v x c w₁ w₂) hbdd
    exact ⟨ω', hω', fun u hu ↦ hωe u (not_not.mpr hu)⟩

end HodgeLean.Foundations.Program
