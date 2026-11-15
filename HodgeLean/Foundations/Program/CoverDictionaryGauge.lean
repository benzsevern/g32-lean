import HodgeLean.Foundations.Program.CoverDictionaryOrders

/-! # B6-5 stage 5d, stage four: gauges and local forms in one complex variable

General statements. If `s = t₀ + κᵉ` with `κ = (z − z₀) l` and `Y' = s' A(s) Y` on a punctured
disc, and a gauge `G` near `t₀` satisfies `G' = A G − (σ − t₀)⁻¹ G Λ`, then `Z = G(s)⁻¹ Y` solves
the Euler system `Z' = e (κ'/κ) Λ Z`, so `Y = G(s) · P · diag(κ^{mᵢ}) · K` with `mᵢ = e dᵢ`
(`caf_gauge_euler`). At a point over `s = ∞` (`1/s = w` analytic, `w(z₀) = 0`) the system is
regular when the residues sum to zero, and `Y = Φ K` with `Φ` analytic and `Φ(z₀) = 1`
(`caf_infty_regular`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Matrix
open scoped Topology
namespace HodgeLean.Foundations.Program

local notation "𝔼" => (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)

/-- From an eventual statement on a punctured neighbourhood to a punctured ball. -/
theorem caf_punctured_ball {P : ℂ → Prop} {z₀ : ℂ} (h : ∀ᶠ z in 𝓝[≠] z₀, P z) :
    ∃ r > 0, ∀ z ∈ ball z₀ r \ {z₀}, P z := by
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp h)
  exact ⟨r, hr, fun z hz ↦ hb z hz.1 hz.2⟩

/-- A punctured ball is a neighbourhood of each of its points. -/
theorem caf_punctured_ball_nhds {z₀ z : ℂ} {r : ℝ} (hz : z ∈ ball z₀ r \ {z₀}) :
    ball z₀ r \ {z₀} ∈ 𝓝 z :=
  (isOpen_ball.sdiff isClosed_singleton).mem_nhds hz

/-- The logarithmic derivative of `t₀ + κᵉ` relative to `κᵉ`. -/
theorem caf_param_ratio (z z₀ : ℂ) (l : ℂ → ℂ) (e : ℕ) (he : 0 < e) (hz : z ≠ z₀) (hlz : l z ≠ 0)
    (dl : ℂ) :
    (e : ℂ) * ((z - z₀) * l z) ^ (e - 1) * (l z + (z - z₀) * dl) *
        (((z - z₀) * l z) ^ e)⁻¹ = e * ((z - z₀)⁻¹ + dl / l z) := by
  have hz' : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
  have hκ : (z - z₀) * l z ≠ 0 := mul_ne_zero hz' hlz
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  field_simp

/-- **The gauge reduction to an Euler system and its solution.** -/
theorem caf_gauge_euler (A Y G : ℂ → 𝔼) (s l : ℂ → ℂ) (z₀ t₀ : ℂ) (e : ℕ) (he : 0 < e)
    (hl : AnalyticAt ℂ l z₀) (hl0 : l z₀ ≠ 0)
    (hs : ∀ᶠ z in 𝓝 z₀, s z = t₀ + ((z - z₀) * l z) ^ e)
    (hY : ∀ᶠ z in 𝓝[≠] z₀, HasDerivAt Y (deriv s z • (A (s z) * Y z)) z ∧ IsUnit (Y z))
    (Λ P : 𝔼) (hP : IsUnit P) (d : Fin 4 → ℂ) (hΛ : Λ * P = P * b65r_operator (diagonal d))
    (hGu : ∀ᶠ σ in 𝓝 t₀, IsUnit (G σ))
    (hG : ∀ᶠ σ in 𝓝[≠] t₀, HasDerivAt G (A σ * G σ - (σ - t₀)⁻¹ • (G σ * Λ)) σ) :
    ∃ m : Fin 4 → ℤ, (∀ i, (e : ℂ) * d i = m i) ∧ ∃ K : 𝔼, IsUnit K ∧
      ∀ᶠ z in 𝓝[≠] z₀, Y z = G (s z) * P *
        b65r_operator (diagonal fun i ↦ ((z - z₀) * l z) ^ (m i)) * K := by
  set κ : ℂ → ℂ := fun z ↦ (z - z₀) * l z
  have hl' : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ l z ∧ l z ≠ 0 :=
    hl.eventually_analyticAt.and (hl.continuousAt.eventually_ne hl0)
  -- the derivative of `s`
  have hsd : ∀ᶠ z in 𝓝 z₀, HasDerivAt s
      ((e : ℂ) * κ z ^ (e - 1) * (l z + (z - z₀) * deriv l z)) z := by
    filter_upwards [hs.eventually_nhds, hl'] with z hz hlz
    have hla := hlz.1
    have hκ : HasDerivAt κ (l z + (z - z₀) * deriv l z) z := by
      have h := ((hasDerivAt_id z).sub_const z₀).mul hla.differentiableAt.hasDerivAt
      rw [show (1 : ℂ) * l z + (id z - z₀) * deriv l z = l z + (z - z₀) * deriv l z by simp] at h
      exact h
    have h2 := (hκ.pow e).const_add t₀
    exact h2.congr_of_eventuallyEq hz
  -- `s` tends to `t₀` from outside `t₀`
  have hscont : ContinuousAt s z₀ := (hsd.self_of_nhds).continuousAt
  have hst : s z₀ = t₀ := by
    rw [hs.self_of_nhds]; simp [zero_pow he.ne']
  have hsne : ∀ᶠ z in 𝓝[≠] z₀, s z ≠ t₀ := by
    filter_upwards [nhdsWithin_le_nhds hs, nhdsWithin_le_nhds hl', self_mem_nhdsWithin]
      with z hz hlz hzz
    rw [hz, add_ne_left]
    exact pow_ne_zero _ (mul_ne_zero (sub_ne_zero.mpr hzz) hlz.2)
  have htend : Tendsto s (𝓝[≠] z₀) (𝓝[≠] t₀) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hsne⟩
    have := hscont.tendsto
    rw [hst] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hGs : ∀ᶠ z in 𝓝[≠] z₀, IsUnit (G (s z)) ∧
      HasDerivAt G (A (s z) * G (s z) - (s z - t₀)⁻¹ • (G (s z) * Λ)) (s z) :=
    have hGu' : ∀ᶠ σ in 𝓝[≠] t₀, IsUnit (G σ) := nhdsWithin_le_nhds hGu
    htend.eventually (hGu'.and hG)
  -- the Euler system for `Z = G(s)⁻¹ Y`
  set Z : ℂ → 𝔼 := fun z ↦ Ring.inverse (G (s z)) * Y z
  have hZ : ∀ᶠ z in 𝓝[≠] z₀,
      HasDerivAt Z (((e : ℂ) * ((z - z₀)⁻¹ + deriv l z / l z)) • (Λ * Z z)) z ∧ IsUnit (Z z) := by
    filter_upwards [hY, hGs, hsne, nhdsWithin_le_nhds hsd, nhdsWithin_le_nhds hs,
      nhdsWithin_le_nhds hl', self_mem_nhdsWithin]
      with z hYz hGz hsz hsdz hsz' hlz' hzz
    obtain ⟨hYd, hYu⟩ := hYz
    obtain ⟨hGu', hGd⟩ := hGz
    have hlz := hlz'.2
    obtain ⟨u, hu⟩ := hGu'
    have hderiv : deriv s z = (e : ℂ) * κ z ^ (e - 1) * (l z + (z - z₀) * deriv l z) :=
      hsdz.deriv
    have hGsd : HasDerivAt (fun w ↦ G (s w))
        (deriv s z • (A (s z) * G (s z) - (s z - t₀)⁻¹ • (G (s z) * Λ))) z := by
      rw [← hderiv] at hsdz
      exact hGd.scomp z hsdz
    have hinv : HasDerivAt (fun w ↦ Ring.inverse (G (s w)))
        (-(↑u⁻¹ * (deriv s z • (A (s z) * G (s z) - (s z - t₀)⁻¹ • (G (s z) * Λ))) * ↑u⁻¹))
        z := by
      have h0 := hasFDerivAt_ringInverse (𝕜 := ℂ) u
      rw [hu] at h0
      convert h0.comp_hasDerivAt z hGsd using 1
      · rfl
      · rw [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply]
    have hratio : deriv s z * (s z - t₀)⁻¹ = (e : ℂ) * ((z - z₀)⁻¹ + deriv l z / l z) := by
      rw [hderiv, hsz', add_sub_cancel_left]
      exact caf_param_ratio z z₀ l e he hzz hlz (deriv l z)
    refine ⟨?_, ?_⟩
    · have h := hinv.mul hYd
      convert h using 1
      rw [← hu, ← hratio]
      simp only [Z, ← hu, Ring.inverse_unit, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
        smul_sub, neg_sub, mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left,
        smul_smul]
      abel
    · simp only [Z, ← hu, Ring.inverse_unit]
      exact (Units.isUnit _).mul hYu
  obtain ⟨r, hr, hball⟩ := caf_punctured_ball hZ
  obtain ⟨m, hm, K, hK, ρ, hρ, hZK⟩ := caf_euler Z z₀ l hl hl0 (e : ℂ) Λ P hP d hΛ r hr
    (fun z hz ↦ (hball z hz).1) (fun z hz ↦ (hball z hz).2)
  refine ⟨m, hm, K, hK, ?_⟩
  filter_upwards [hGs, nhdsWithin_le_nhds (ball_mem_nhds z₀ hρ), self_mem_nhdsWithin]
    with z hGz hzρ hzz
  have hGu' := hGz.1
  have := hZK z ⟨hzρ, hzz⟩
  obtain ⟨u, hu⟩ := hGu'
  have hY' : Y z = G (s z) * Z z := by
    simp only [Z, ← hu, Ring.inverse_unit, Units.mul_inv_cancel_left]
  rw [hY', this]
  simp only [mul_assoc]


/-- The coefficient at `s = 1/w` times `ds/dz` is the regular coefficient at infinity, when the
residues sum to zero. -/
theorem caf_infty_coefficient {ι : Type*} [Fintype ι] (t : ι → ℂ) (R : ι → 𝔼)
    (hR : ∑ q, R q = 0) (w dw : ℂ) (hw : w ≠ 0) (ht : ∀ q, 1 - t q * w ≠ 0) :
    (-dw / w ^ 2) • b65p_coefficient (Fin 4 → ℂ) t R w⁻¹ =
      -dw • ∑ q, (t q / (1 - t q * w)) • R q := by
  have hterm : ∀ q, (-dw / w ^ 2) * (w⁻¹ - t q)⁻¹ = -dw * (t q / (1 - t q * w)) + (-dw / w) := by
    intro q
    have h1 : w⁻¹ - t q = (1 - t q * w) / w := by field_simp
    rw [h1]
    have : 1 - w * t q ≠ 0 := by rw [mul_comm]; exact ht q
    field_simp
    ring
  calc (-dw / w ^ 2) • b65p_coefficient (Fin 4 → ℂ) t R w⁻¹ =
        ∑ q, ((-dw / w ^ 2) * (w⁻¹ - t q)⁻¹) • R q := by
        rw [b65p_coefficient, Finset.smul_sum]; simp_rw [smul_smul]
    _ = ∑ q, ((-dw * (t q / (1 - t q * w))) • R q + (-dw / w) • R q) := by
        simp_rw [hterm, add_smul]
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.smul_sum, hR, smul_zero, add_zero, Finset.smul_sum]
        simp_rw [smul_smul]

/-- **The regular local form over `s = ∞`.** If `1/s = w` with `w` analytic and `w(z₀) = 0`,
the residues sum to zero and `Y' = s' A(s) Y` with `Y` invertible on a punctured disc, then
`Y = Φ K` there with `Φ` analytic at `z₀`, `Φ(z₀) = 1` and `K` invertible. -/
theorem caf_infty_regular {ι : Type*} [Fintype ι] (t : ι → ℂ) (R : ι → 𝔼) (hR : ∑ q, R q = 0)
    (Y : ℂ → 𝔼) (s w : ℂ → ℂ) (z₀ : ℂ) (hw : AnalyticAt ℂ w z₀) (hw0 : w z₀ = 0)
    (hsw : ∀ᶠ z in 𝓝[≠] z₀, w z ≠ 0 ∧ s z = (w z)⁻¹)
    (hY : ∀ᶠ z in 𝓝[≠] z₀,
      HasDerivAt Y (deriv s z • (b65p_coefficient (Fin 4 → ℂ) t R (s z) * Y z)) z ∧
        IsUnit (Y z)) :
    ∃ Φ : ℂ → 𝔼, AnalyticAt ℂ Φ z₀ ∧ Φ z₀ = 1 ∧ ∃ K : 𝔼, IsUnit K ∧
      ∀ᶠ z in 𝓝[≠] z₀, Y z = Φ z * K := by
  set B : ℂ → 𝔼 := fun z ↦ -deriv w z • ∑ q, (t q / (1 - t q * w z)) • R q
  have hB : AnalyticAt ℂ B z₀ := by
    have hq : ∀ q, AnalyticAt ℂ (fun z ↦ (t q / (1 - t q * w z)) • R q) z₀ := by
      intro q
      have h1 : AnalyticAt ℂ (fun z ↦ t q / (1 - t q * w z)) z₀ :=
        analyticAt_const.div (analyticAt_const.sub (analyticAt_const.mul hw)) (by simp [hw0])
      exact h1.smul (analyticAt_const (v := R q))
    have hsum : AnalyticAt ℂ (fun z ↦ ∑ q, (t q / (1 - t q * w z)) • R q) z₀ :=
      Finset.analyticAt_fun_sum _ fun q _ ↦ hq q
    have hd : AnalyticAt ℂ (fun z ↦ -deriv w z) z₀ := hw.deriv.neg
    exact hd.smul hsum
  have hBev := hB.eventually_analyticAt
  obtain ⟨r, hr, hBr⟩ := Metric.eventually_nhds_iff_ball.mp hBev
  obtain ⟨hΦa, hΦ1, -, hΦd, hΦu⟩ := b65f_segment_solution (Fin 4 → ℂ) B z₀ r hr
    (fun z hz ↦ hBr z hz)
  -- the system is `Y' = B Y` on a punctured disc
  have hwt : ∀ᶠ z in 𝓝 z₀, ∀ q, 1 - t q * w z ≠ 0 := by
    have : ∀ q, ∀ᶠ z in 𝓝 z₀, 1 - t q * w z ≠ 0 := fun q ↦
      ((continuousAt_const.sub (continuousAt_const.mul hw.continuousAt)).eventually_ne
        (by simp [hw0]))
    exact Filter.eventually_all.mpr this
  have hYB : ∀ᶠ z in 𝓝[≠] z₀, HasDerivAt Y (B z * Y z) z ∧ IsUnit (Y z) := by
    have hsw' : ∀ᶠ z in 𝓝[≠] z₀, ∀ᶠ y in 𝓝 z, w y ≠ 0 ∧ s y = (w y)⁻¹ := by
      have := eventually_nhdsWithin_iff.mp hsw
      filter_upwards [nhdsWithin_le_nhds this.eventually_nhds, self_mem_nhdsWithin] with z hz hzz
      filter_upwards [hz, isOpen_compl_singleton.mem_nhds hzz] with y hy hyy
      exact hy hyy
    filter_upwards [hY, hsw', hsw, nhdsWithin_le_nhds hwt, nhdsWithin_le_nhds hw.eventually_analyticAt]
      with z hYz hsz hswz hwtz hwa
    refine ⟨?_, hYz.2⟩
    have hds : deriv s z = -deriv w z / w z ^ 2 := by
      have h1 : HasDerivAt (fun y ↦ (w y)⁻¹) (-deriv w z / w z ^ 2) z :=
        hwa.differentiableAt.hasDerivAt.inv hswz.1
      have h2 : s =ᶠ[𝓝 z] fun y ↦ (w y)⁻¹ := hsz.mono fun y hy ↦ hy.2
      exact (h1.congr_of_eventuallyEq h2).deriv
    have h := hYz.1
    rw [hds, hswz.2, ← smul_mul_assoc, caf_infty_coefficient t R hR (w z) (deriv w z) hswz.1 hwtz]
      at h
    exact h
  obtain ⟨ρ, hρ, hball⟩ := caf_punctured_ball hYB
  set ρ' := min ρ r
  have hρ' : 0 < ρ' := lt_min hρ hr
  have hU : IsOpen (ball z₀ ρ' \ {z₀}) := isOpen_ball.sdiff isClosed_singleton
  have hsub : ∀ z ∈ ball z₀ ρ' \ {z₀}, z ∈ ball z₀ ρ \ {z₀} ∧ z ∈ ball z₀ r := fun z hz ↦
    ⟨⟨ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩, ball_subset_ball (min_le_right _ _) hz.1⟩
  obtain ⟨K, hK⟩ := caf_eq_mul_const_of_ode (ball z₀ ρ' \ {z₀}) hU
    (caf_isPreconnected_ball_diff z₀ hρ') B Y (b65f_segment (Fin 4 → ℂ) B z₀)
    (fun z hz ↦ (hball z (hsub z hz).1).1) (fun z hz ↦ hΦd z (hsub z hz).2)
    (fun z hz ↦ hΦu z (hsub z hz).2)
  refine ⟨b65f_segment (Fin 4 → ℂ) B z₀, hΦa z₀ (mem_ball_self hr), hΦ1, K, ?_, ?_⟩
  · obtain ⟨z₁, hz₁⟩ : (ball z₀ ρ' \ {z₀}).Nonempty := by
      refine ⟨z₀ + (ρ' / 2 : ℝ), ?_, ?_⟩
      · simp [dist_eq_norm, abs_of_pos hρ', hρ']
      · simp [hρ'.ne']
    obtain ⟨u, hu⟩ := hΦu z₁ (hsub z₁ hz₁).2
    have hK' : K = ↑u⁻¹ * Y z₁ := by
      rw [hK z₁ hz₁, ← hu, Units.inv_mul_cancel_left]
    rw [hK']
    exact (Units.isUnit _).mul (hball z₁ (hsub z₁ hz₁).1).2
  · filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds z₀ hρ'), self_mem_nhdsWithin] with z hz hzz
    exact hK z ⟨hz, hzz⟩

end HodgeLean.Foundations.Program
