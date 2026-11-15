import HodgeLean.Foundations.Program.CoverAnalyticTwo
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # B6-5 stage 5d, stage four: roots and Euler systems in one complex variable

General statements. A holomorphic function with a zero of order `e` is locally the `e`-th power
of a function with a simple zero (`caf_root_factor`). For such a local parameter `κ`, a
holomorphic vector function on a punctured disc solving `w' = μ (κ'/κ) w` without zeros is
`κ^m k` with `m = μ ∈ ℤ` (`caf_euler_row`); a holomorphic invertible operator function solving
`Z' = e (κ'/κ) Λ Z`, with `Λ` diagonalized by `P`, is `P · diag(κ^{m_i}) · K` with
`m_i = e d_i ∈ ℤ` (`caf_euler`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Matrix
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- **A holomorphic `e`-th root** of a function analytic and nonzero at a point. -/
theorem caf_analytic_root (u : ℂ → ℂ) (z₀ : ℂ) (hu : AnalyticAt ℂ u z₀) (h0 : u z₀ ≠ 0)
    (e : ℕ) (he : e ≠ 0) :
    ∃ l : ℂ → ℂ, AnalyticAt ℂ l z₀ ∧ l z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, u z = l z ^ e := by
  set c := u z₀ ^ ((e : ℂ)⁻¹)
  have hc : c ^ e = u z₀ := Complex.cpow_nat_inv_pow _ he
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow he] at hc
    exact h0 hc.symm
  set v := fun z ↦ u z / u z₀
  have hv : AnalyticAt ℂ v z₀ := hu.div analyticAt_const h0
  have hv1 : v z₀ = 1 := div_self h0
  have hslit : v z₀ ∈ Complex.slitPlane := by rw [hv1]; exact Complex.one_mem_slitPlane
  have hlog : AnalyticAt ℂ (fun z ↦ Complex.log (v z)) z₀ := hv.clog hslit
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he
  refine ⟨fun z ↦ c * Complex.exp (Complex.log (v z) / e), ?_, ?_, ?_⟩
  · exact analyticAt_const.mul ((hlog.div analyticAt_const he').cexp)
  · exact mul_ne_zero hc0 (Complex.exp_ne_zero _)
  · have hev : ∀ᶠ z in 𝓝 z₀, v z ≠ 0 :=
      hv.continuousAt.eventually_ne (by rw [hv1]; exact one_ne_zero)
    filter_upwards [hev] with z hz
    rw [mul_pow, hc, ← Complex.exp_nat_mul, mul_div_cancel₀ _ he', Complex.exp_log hz]
    simp only [v]
    field_simp

/-- **Root factorization.** A function analytic and not locally constant at `z₀` is locally
`f z₀ + ((z − z₀) l z)^e` with `e > 0` its order and `l` analytic and nonzero at `z₀`. -/
theorem caf_root_factor (f : ℂ → ℂ) (z₀ : ℂ) (hf : AnalyticAt ℂ f z₀)
    (hnc : ¬ EventuallyConst f (𝓝 z₀)) :
    ∃ e : ℕ, 0 < e ∧ analyticOrderAt (fun z ↦ f z - f z₀) z₀ = e ∧
      ∃ l : ℂ → ℂ, AnalyticAt ℂ l z₀ ∧ l z₀ ≠ 0 ∧
        ∀ᶠ z in 𝓝 z₀, f z = f z₀ + ((z - z₀) * l z) ^ e := by
  rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top] at hnc
  have hfs : AnalyticAt ℂ (fun z ↦ f z - f z₀) z₀ := hf.sub analyticAt_const
  obtain ⟨g, hg, hg0, hfg⟩ := hfs.analyticOrderAt_ne_top.mp hnc
  set e := analyticOrderNatAt (fun z ↦ f z - f z₀) z₀
  have he : analyticOrderAt (fun z ↦ f z - f z₀) z₀ = e :=
    (ENat.natCast_toNat hnc).symm
  have hepos : 0 < e := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    have : analyticOrderAt (fun z ↦ f z - f z₀) z₀ ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hfs, by simp⟩
    rw [he, h0] at this
    exact this rfl
  obtain ⟨l, hl, hl0, hlg⟩ := caf_analytic_root g z₀ hg hg0 e hepos.ne'
  refine ⟨e, hepos, he, l, hl, hl0, ?_⟩
  filter_upwards [hfg, hlg] with z h1 h2
  rw [mul_pow, ← h2, ← smul_eq_mul, ← h1]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **One row of an Euler system.** Let `κ = (z − z₀) l`, `l` analytic and nonzero at `z₀`. A
function without zeros on a punctured disc solving `w' = μ (κ'/κ) w` there is `κ^m k` near `z₀`,
with `μ = m ∈ ℤ`. -/
theorem caf_euler_row [FiniteDimensional ℂ E] (w : ℂ → E) (z₀ : ℂ) (l : ℂ → ℂ)
    (hl : AnalyticAt ℂ l z₀) (hl0 : l z₀ ≠ 0) (μ : ℂ) (r : ℝ) (hr : 0 < r)
    (hode : ∀ z ∈ ball z₀ r \ {z₀},
      HasDerivAt w ((μ * ((z - z₀)⁻¹ + deriv l z / l z)) • w z) z)
    (hne : ∀ z ∈ ball z₀ r \ {z₀}, w z ≠ 0) :
    ∃ m : ℤ, μ = m ∧ ∃ k : E, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z ∈ ball z₀ ρ \ {z₀}, w z = ((z - z₀) * l z) ^ m • k := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  -- a disc on which `l` is analytic, nonzero, and `l'/l` is bounded
  have hq : ContinuousAt (fun z ↦ deriv l z / l z) z₀ :=
    (hl.deriv.continuousAt).div hl.continuousAt hl0
  obtain ⟨r₁, hr₁, hball₁⟩ : ∃ r₁ > 0, ∀ z ∈ ball z₀ r₁, AnalyticAt ℂ l z ∧ l z ≠ 0 ∧
      ‖deriv l z / l z‖ ≤ ‖deriv l z₀ / l z₀‖ + 1 := by
    have h1 := hl.eventually_analyticAt
    have h2 := hl.continuousAt.eventually_ne hl0
    have h3 : ∀ᶠ z in 𝓝 z₀, ‖deriv l z / l z‖ ≤ ‖deriv l z₀ / l z₀‖ + 1 := by
      have := hq.norm.eventually (gt_mem_nhds (lt_add_one ‖deriv l z₀ / l z₀‖))
      filter_upwards [this] with z hz using hz.le
    obtain ⟨r₁, hr₁, h⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and (h2.and h3))
    exact ⟨r₁, hr₁, fun z hz ↦ h z hz⟩
  set ρ := min r r₁
  have hρ : 0 < ρ := lt_min hr hr₁
  have hρr : ball z₀ ρ \ {z₀} ⊆ ball z₀ r \ {z₀} :=
    sdiff_subset_sdiff_left (ball_subset_ball (min_le_left _ _))
  have hρr₁ : ball z₀ ρ ⊆ ball z₀ r₁ := ball_subset_ball (min_le_right _ _)
  set Q := ‖deriv l z₀ / l z₀‖ + 1
  -- meromorphy
  have hmero : MeromorphicAt w z₀ := by
    refine caf_meromorphicAt_of_linear_ode w
      (fun z ↦ (μ * ((z - z₀)⁻¹ + deriv l z / l z)) • ContinuousLinearMap.id ℂ E) z₀ ρ
      (‖μ‖ * (1 + Q * ρ)) hρ (fun z hz ↦ by simpa using hode z (hρr hz)) ?_
    intro z hz
    have hz0 : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz.2)
    have hzρ : ‖z - z₀‖ < ρ := by simpa [dist_eq_norm] using hz.1
    have hQ := (hball₁ z (hρr₁ hz.1)).2.2
    calc ‖(μ * ((z - z₀)⁻¹ + deriv l z / l z)) • ContinuousLinearMap.id ℂ E‖
        ≤ ‖μ * ((z - z₀)⁻¹ + deriv l z / l z)‖ * ‖ContinuousLinearMap.id ℂ E‖ :=
          norm_smul_le _ _
      _ ≤ ‖μ * ((z - z₀)⁻¹ + deriv l z / l z)‖ * 1 := by
          gcongr
          exact ContinuousLinearMap.norm_id_le
      _ = ‖μ‖ * ‖(z - z₀)⁻¹ + deriv l z / l z‖ := by rw [mul_one, norm_mul]
      _ ≤ ‖μ‖ * (‖z - z₀‖⁻¹ + Q) := by
          gcongr
          exact (norm_add_le _ _).trans (by rw [norm_inv]; gcongr)
      _ ≤ ‖μ‖ * (1 + Q * ρ) / ‖z - z₀‖ := by
          rw [mul_div_assoc]
          gcongr
          rw [le_div_iff₀ hz0, add_mul, inv_mul_cancel₀ hz0.ne']
          have : 0 ≤ Q := by positivity
          nlinarith
  -- the order is finite
  have hne' : ¬ ∀ᶠ z in 𝓝[≠] z₀, w z = 0 := by
    intro h
    have hm : ∀ᶠ z in 𝓝[≠] z₀, z ∈ ball z₀ ρ \ {z₀} := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds z₀ hρ)]
        with z h1 h2 using ⟨h2, h1⟩
    obtain ⟨z, hz, hz'⟩ := (h.and hm).exists
    exact hne z (hρr hz') hz
  obtain ⟨m, hm⟩ : ∃ m : ℤ, meromorphicOrderAt w z₀ = m := by
    have : meromorphicOrderAt w z₀ ≠ ⊤ := fun h ↦ hne' (meromorphicOrderAt_eq_top_iff.mp h)
    exact ⟨_, (WithTop.coe_untop _ this).symm⟩
  -- the indicial equation
  have hode' : ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) • deriv w z =
      (μ • ContinuousLinearMap.id ℂ E) (w z) +
        (z - z₀) • ((μ * (deriv l z / l z)) • ContinuousLinearMap.id ℂ E) (w z) := by
    have hm' : ∀ᶠ z in 𝓝[≠] z₀, z ∈ ball z₀ ρ \ {z₀} := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds z₀ hρ)]
        with z h1 h2 using ⟨h2, h1⟩
    filter_upwards [hm'] with z hz
    rw [(hode z (hρr hz)).deriv]
    have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hz.2
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    rw [← add_smul]
    congr 1
    field_simp
  have hμ : μ = m := by
    obtain ⟨v, hv, hv'⟩ := caf_order_eigenvalue w z₀ (μ • ContinuousLinearMap.id ℂ E)
      (fun z ↦ (μ * (deriv l z / l z)) • ContinuousLinearMap.id ℂ E) m hmero hm
      ((continuousAt_const.mul hq).smul continuousAt_const) hode'
    have : (μ - m) • v = 0 := by rw [sub_smul, sub_eq_zero]; simpa using hv'
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hv)
  -- `κ^{-m} w` is constant on the punctured disc
  set κ : ℂ → ℂ := fun z ↦ (z - z₀) * l z
  have hκ0 : ∀ z ∈ ball z₀ ρ \ {z₀}, κ z ≠ 0 := fun z hz ↦
    mul_ne_zero (sub_ne_zero.mpr hz.2) (hball₁ z (hρr₁ hz.1)).2.1
  have hκd : ∀ z ∈ ball z₀ ρ, HasDerivAt κ (l z + (z - z₀) * deriv l z) z := by
    intro z hz
    have hlz := ((hball₁ z (hρr₁ hz)).1.differentiableAt).hasDerivAt
    have h := ((hasDerivAt_id z).sub_const z₀).mul hlz
    simp only [id, one_mul] at h
    exact h
  set k : ℂ → E := fun z ↦ κ z ^ (-m) • w z
  have hkd : ∀ z ∈ ball z₀ ρ \ {z₀}, HasDerivAt k 0 z := by
    intro z hz
    have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hz.2
    have hlz := (hball₁ z (hρr₁ hz.1)).2.1
    have h1 : HasDerivAt (fun z ↦ κ z ^ (-m))
        (((-m : ℤ) : ℂ) * κ z ^ (-m - 1) * (l z + (z - z₀) * deriv l z)) z :=
      (hasDerivAt_zpow (-m) (κ z) (Or.inl (hκ0 z hz))).comp z (hκd z hz.1)
    have h2 := h1.smul (hode z (hρr hz))
    convert h2 using 1
    rw [smul_smul, ← add_smul]
    symm
    convert zero_smul ℂ (w z) using 1
    have hX : (κ z)⁻¹ * (l z + (z - z₀) * deriv l z) = (z - z₀)⁻¹ + deriv l z / l z := by
      simp only [κ]
      field_simp
    rw [zpow_sub₀ (hκ0 z hz), zpow_one, hμ]
    have : ((-m : ℤ) : ℂ) * (κ z ^ (-m) / κ z) * (l z + (z - z₀) * deriv l z) =
        -(m : ℂ) * κ z ^ (-m) * ((z - z₀)⁻¹ + deriv l z / l z) := by
      rw [← hX]; push_cast; ring
    rw [this]
    ring_nf
  obtain ⟨z₁, hz₁⟩ : (ball z₀ ρ \ {z₀}).Nonempty := by
    refine ⟨z₀ + (ρ / 2 : ℝ), ?_, ?_⟩
    · simp [dist_eq_norm, abs_of_pos hρ, hρ]
    · simp [hρ.ne']
  have hopen : IsOpen (ball z₀ ρ \ {z₀}) := isOpen_ball.sdiff isClosed_singleton
  refine ⟨m, hμ, k z₁, ρ, hρ, fun z hz ↦ ?_⟩
  have hconst := hopen.is_const_of_deriv_eq_zero (caf_isPreconnected_ball_diff z₀ hρ)
    (fun w hw ↦ (hkd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hkd w hw).deriv) hz hz₁
  rw [← hconst]
  show w z = κ z ^ m • κ z ^ (-m) • w z
  rw [smul_smul, ← zpow_add₀ (hκ0 z hz), add_neg_cancel, zpow_zero, one_smul]

local notation "𝔼" => (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)

/-- Row `i` of the matrix of an operator on `ℂ⁴`, as a continuous linear map.
Source: `b65q_mat`, `b65q_entryCLM`. -/
def caf_row (i : Fin 4) : 𝔼 →L[ℂ] (Fin 4 → ℂ) :=
  ContinuousLinearMap.pi fun j ↦ b65q_entryCLM i j

theorem caf_row_apply (i : Fin 4) (T : 𝔼) : caf_row i T = fun j ↦ b65q_mat T i j := by
  funext j
  simp [caf_row, b65q_entryCLM_apply]

theorem caf_row_diag_mul (i : Fin 4) (d : Fin 4 → ℂ) (T : 𝔼) :
    caf_row i (b65r_operator (diagonal d) * T) = d i • caf_row i T := by
  rw [caf_row_apply, caf_row_apply]
  funext j
  have h := congrArg (fun M ↦ M i j) (map_mul b65q_matAlg (b65r_operator (diagonal d)) T)
  simp only [b65q_matAlg_apply, b65q_mat_operator] at h
  rw [h]
  simp [diagonal_mul]

/-- A row of an invertible operator is nonzero. -/
theorem caf_row_ne_zero (i : Fin 4) {T : 𝔼} (hT : IsUnit T) : caf_row i T ≠ 0 := by
  intro h
  have hm : IsUnit (b65q_mat T) := hT.map b65q_matAlg
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hm
  have hrow : (b65q_mat T) i = 0 := by
    rw [caf_row_apply] at h
    funext j
    exact congrFun h j
  rw [Matrix.det_eq_zero_of_row_eq_zero i (fun j ↦ by rw [hrow]; rfl)] at hdet
  exact not_isUnit_zero hdet

/-- **Euler systems.** Let `κ = (z − z₀) l`, `l` analytic and nonzero at `z₀`, and `Λ P = P D`
with `P` invertible and `D = diag(d)`. An invertible solution of `Z' = e (κ'/κ) Λ Z` on a punctured
disc is `P · diag(κ^{m_i}) · K` near `z₀`, with `K` invertible and `e d_i = m_i ∈ ℤ`. -/
theorem caf_euler (Z : ℂ → 𝔼) (z₀ : ℂ) (l : ℂ → ℂ) (hl : AnalyticAt ℂ l z₀) (hl0 : l z₀ ≠ 0)
    (e : ℂ) (Λ P : 𝔼) (hP : IsUnit P) (d : Fin 4 → ℂ)
    (hΛ : Λ * P = P * b65r_operator (diagonal d)) (r : ℝ) (hr : 0 < r)
    (hZ : ∀ z ∈ ball z₀ r \ {z₀},
      HasDerivAt Z ((e * ((z - z₀)⁻¹ + deriv l z / l z)) • (Λ * Z z)) z)
    (hu : ∀ z ∈ ball z₀ r \ {z₀}, IsUnit (Z z)) :
    ∃ m : Fin 4 → ℤ, (∀ i, e * d i = m i) ∧ ∃ K : 𝔼, IsUnit K ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z ∈ ball z₀ ρ \ {z₀},
        Z z = P * b65r_operator (diagonal fun i ↦ ((z - z₀) * l z) ^ (m i)) * K := by
  obtain ⟨Pu, rfl⟩ := hP
  set D := b65r_operator (diagonal d)
  have hPΛ : (↑Pu⁻¹ : 𝔼) * Λ = D * ↑Pu⁻¹ := by
    calc (↑Pu⁻¹ : 𝔼) * Λ = ↑Pu⁻¹ * (Λ * ↑Pu) * ↑Pu⁻¹ := by
          simp [mul_assoc]
      _ = D * ↑Pu⁻¹ := by rw [hΛ]; simp [← mul_assoc]
  set W : ℂ → 𝔼 := fun z ↦ ↑Pu⁻¹ * Z z
  have hW : ∀ z ∈ ball z₀ r \ {z₀},
      HasDerivAt W ((e * ((z - z₀)⁻¹ + deriv l z / l z)) • (D * W z)) z := by
    intro z hz
    have h := (hZ z hz).const_mul (↑Pu⁻¹ : 𝔼)
    convert h using 1
    rw [mul_smul_comm, ← mul_assoc (↑Pu⁻¹ : 𝔼) Λ, hPΛ, mul_assoc]
  have hWu : ∀ z ∈ ball z₀ r \ {z₀}, IsUnit (W z) := fun z hz ↦
    (Units.isUnit _).mul (hu z hz)
  have hrow : ∀ i : Fin 4, ∃ m : ℤ, e * d i = m ∧ ∃ k : Fin 4 → ℂ, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z ∈ ball z₀ ρ \ {z₀}, caf_row i (W z) = ((z - z₀) * l z) ^ m • k := by
    intro i
    refine caf_euler_row (fun z ↦ caf_row i (W z)) z₀ l hl hl0 (e * d i) r hr ?_
      (fun z hz ↦ caf_row_ne_zero i (hWu z hz))
    intro z hz
    have h := (caf_row i).hasFDerivAt.comp_hasDerivAt z (hW z hz)
    rw [ContinuousLinearMap.map_smul, caf_row_diag_mul, smul_smul] at h
    convert h using 1
    · congr 1
    · congr 1
      ring
  choose m hm k ρf hρf hk using hrow
  obtain ⟨r₂, hr₂, hl₂⟩ := Metric.eventually_nhds_iff_ball.mp (hl.continuousAt.eventually_ne hl0)
  set ρ := min (min r r₂) (Finset.univ.inf' Finset.univ_nonempty ρf)
  have hρ : 0 < ρ := by
    refine lt_min (lt_min hr hr₂) ?_
    rw [Finset.lt_inf'_iff]
    exact fun i _ ↦ hρf i
  have hρi : ∀ i, ball z₀ ρ \ {z₀} ⊆ ball z₀ (ρf i) \ {z₀} := fun i ↦
    sdiff_subset_sdiff_left (ball_subset_ball ((min_le_right _ _).trans
      (Finset.inf'_le _ (Finset.mem_univ i))))
  have hρr : ball z₀ ρ \ {z₀} ⊆ ball z₀ r \ {z₀} :=
    sdiff_subset_sdiff_left (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)))
  have hκ0 : ∀ z ∈ ball z₀ ρ \ {z₀}, (z - z₀) * l z ≠ 0 := fun z hz ↦
    mul_ne_zero (sub_ne_zero.mpr hz.2)
      (hl₂ z (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hz.1))
  set K : 𝔼 := b65r_operator (Matrix.of fun i j ↦ k i j)
  set Dκ : ℂ → 𝔼 := fun z ↦ b65r_operator (diagonal fun i ↦ ((z - z₀) * l z) ^ (m i))
  have hWK : ∀ z ∈ ball z₀ ρ \ {z₀}, W z = Dκ z * K := by
    intro z hz
    apply b65q_mat_injective
    rw [show b65q_mat (Dκ z * K) = b65q_mat (Dκ z) * b65q_mat K from
      map_mul b65q_matAlg (Dκ z) K, b65q_mat_operator, b65q_mat_operator]
    ext i j
    have := congrFun (hk i z (hρi i hz)) j
    rw [caf_row_apply] at this
    simp only at this
    rw [this, diagonal_mul]
    simp
  obtain ⟨z₁, hz₁⟩ : (ball z₀ ρ \ {z₀}).Nonempty := by
    refine ⟨z₀ + (ρ / 2 : ℝ), ?_, ?_⟩
    · simp [dist_eq_norm, abs_of_pos hρ, hρ]
    · simp [hρ.ne']
  set Dinv : 𝔼 := b65r_operator (diagonal fun i ↦ ((z₁ - z₀) * l z₁) ^ (-m i))
  have h1 : Dinv * Dκ z₁ = 1 := by
    apply b65q_mat_injective
    rw [show b65q_mat (_ * _) = b65q_mat _ * b65q_mat _ from map_mul b65q_matAlg _ _,
      b65q_mat_operator, b65q_mat_operator, diagonal_mul_diagonal,
      show b65q_mat 1 = 1 from map_one b65q_matAlg]
    congr 1
    funext i
    rw [← zpow_add₀ (hκ0 z₁ hz₁), neg_add_cancel, zpow_zero]
  have h2 : Dκ z₁ * Dinv = 1 := by
    apply b65q_mat_injective
    rw [show b65q_mat (_ * _) = b65q_mat _ * b65q_mat _ from map_mul b65q_matAlg _ _,
      b65q_mat_operator, b65q_mat_operator, diagonal_mul_diagonal,
      show b65q_mat 1 = 1 from map_one b65q_matAlg]
    congr 1
    funext i
    rw [← zpow_add₀ (hκ0 z₁ hz₁), add_neg_cancel, zpow_zero]
  have hK : K = Dinv * W z₁ := by
    rw [hWK z₁ hz₁, ← mul_assoc, h1, one_mul]
  refine ⟨m, hm, K, ?_, ρ, hρ, fun z hz ↦ ?_⟩
  · rw [hK]
    exact (Units.isUnit ⟨Dinv, Dκ z₁, h1, h2⟩).mul (hWu z₁ (hρr hz₁))
  · have : Z z = ↑Pu * W z := by simp [W, ← mul_assoc]
    rw [this, hWK z hz, mul_assoc]

end HodgeLean.Foundations.Program
