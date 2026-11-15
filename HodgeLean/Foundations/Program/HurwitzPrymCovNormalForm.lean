import HodgeLean.Foundations.Program.HurwitzPrymDefs

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-cov`: the local normal form `t ↦ t^e` in one variable

An analytic `h : ℂ → ℂ` with `h 0 = 0` and analytic order `e ≥ 1` at `0` is `k^e` for a local
biholomorphism `k` (an `e`-th root of the unit factor exists near `0`). Hence on small balls every
small nonzero value has exactly `e` preimages, all with nonzero derivative, and `0` has only `0`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology Metric

namespace HodgeLean.Foundations.Program

/-- **An `e`-th root of a nonvanishing analytic function near a point.** -/
theorem b4cov_exists_root {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) {e : ℕ}
    (he : 0 < e) : ∃ v : ℂ → ℂ, AnalyticAt ℂ v 0 ∧ v 0 ≠ 0 ∧ ∀ᶠ t in 𝓝 0, v t ^ e = u t := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (u 0) he
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hu0 (by rw [← hc, zero_pow he.ne'])
  let q : ℂ → ℂ := fun t ↦ u t / u 0
  have hq : AnalyticAt ℂ q 0 := hu.div analyticAt_const hu0
  have hq0 : q 0 = 1 := div_self hu0
  have hlog : AnalyticAt ℂ (fun t ↦ Complex.log (q t)) 0 :=
    (analyticAt_clog (by rw [hq0]; exact Complex.one_mem_slitPlane)).comp hq
  refine ⟨fun t ↦ c * Complex.exp (Complex.log (q t) / e), ?_, ?_, ?_⟩
  · exact analyticAt_const.mul (analyticAt_cexp.comp (hlog.div analyticAt_const
      (Nat.cast_ne_zero.2 he.ne')))
  · simp only [hq0, Complex.log_one, zero_div, Complex.exp_zero, mul_one]
    exact hc0
  · have hne : ∀ᶠ t in 𝓝 (0 : ℂ), q t ≠ 0 :=
      hq.continuousAt.eventually_ne (by rw [hq0]; exact one_ne_zero)
    filter_upwards [hne] with t ht
    rw [mul_pow, ← Complex.exp_nat_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 he.ne'),
      Complex.exp_log ht, hc]
    simp only [q]
    field_simp

/-- A nonzero complex number has exactly `e` distinct `e`-th roots. -/
theorem b4cov_card_nthRootsFinset {e : ℕ} (he : 0 < e) {w : ℂ} (hw : w ≠ 0) :
    (Polynomial.nthRootsFinset e w).card = e := by
  classical
  have hζ := Complex.isPrimitiveRoot_exp e he.ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq w he
  rw [Polynomial.nthRootsFinset, ← Multiset.toFinset_eq (hζ.nthRoots_nodup hw), Finset.card_mk,
    hζ.card_nthRoots, if_pos ⟨α, hα⟩]

/-- **Counting preimages for the normal form `t ↦ t^e`.** -/
theorem b4cov_count {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) {e : ℕ} (he : 0 < e)
    (hord : analyticOrderAt h 0 = e) (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ r, 0 < r ∧ r ≤ r₀ ∧ ∃ ρ, 0 < ρ ∧ (∀ t ∈ ball (0 : ℂ) r, h t = 0 → t = 0) ∧
      ∀ w : ℂ, w ≠ 0 → ‖w‖ < ρ →
        {t ∈ ball (0 : ℂ) r | h t = w}.ncard = e ∧
          ∀ t ∈ ball (0 : ℂ) r, h t = w → deriv h t ≠ 0 := by
  obtain ⟨u, hu, hu0, hfu⟩ := hh.analyticOrderAt_eq_natCast.1 hord
  obtain ⟨v, hv, hv0, hvu⟩ := b4cov_exists_root hu hu0 he
  let k : ℂ → ℂ := fun t ↦ t * v t
  have hk : AnalyticAt ℂ k 0 := analyticAt_id.mul hv
  have hkd : HasDerivAt k (v 0) 0 := by
    have := (hasDerivAt_id' (0 : ℂ)).mul hv.differentiableAt.hasDerivAt
    simp only [one_mul, zero_mul, add_zero] at this
    exact this
  have hks : HasStrictDerivAt k (v 0) 0 := by
    have := hk.hasStrictDerivAt
    rwa [hkd.deriv] at this
  have hhk : ∀ᶠ t in 𝓝 (0 : ℂ), h t = k t ^ e := by
    filter_upwards [hfu, hvu] with t h1 h2
    rw [h1, sub_zero, smul_eq_mul, ← h2, mul_pow]
  let K := (hks.hasStrictFDerivAt_equiv hv0).toOpenPartialHomeomorph k
  have hK : (K : ℂ → ℂ) = k := (hks.hasStrictFDerivAt_equiv hv0).toOpenPartialHomeomorph_coe
  have hK0 : (0 : ℂ) ∈ K.source := (hks.hasStrictFDerivAt_equiv hv0).mem_toOpenPartialHomeomorph_source
  have hdk : ∀ᶠ t in 𝓝 (0 : ℂ), deriv k t ≠ 0 :=
    hk.deriv.continuousAt.eventually_ne (by rw [hkd.deriv]; exact hv0)
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ K.source ∧ h t = k t ^ e ∧ deriv k t ≠ 0 ∧
      AnalyticAt ℂ k t :=
    Filter.Eventually.and (K.open_source.mem_nhds hK0 : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ K.source)
      (hhk.and (hdk.and hk.eventually_analyticAt))
  obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set r := min r₀ r₁
  have hr : 0 < r := lt_min hr₀ hr₁
  have hrsub : ball (0 : ℂ) r ⊆ ball 0 r₁ := ball_subset_ball (min_le_right _ _)
  have hsrc : ball (0 : ℂ) r ⊆ K.source := fun t ht ↦ (hball t (hrsub ht)).1
  have hderiv : ∀ t ∈ ball (0 : ℂ) r, deriv h t = (e : ℂ) * k t ^ (e - 1) * deriv k t := by
    intro t ht
    have heq : h =ᶠ[𝓝 t] fun s ↦ k s ^ e := by
      filter_upwards [isOpen_ball.mem_nhds (hrsub ht)] with s hs
      exact (hball s hs).2.1
    rw [heq.deriv_eq]
    have hkt : DifferentiableAt ℂ k t := (hball t (hrsub ht)).2.2.2.differentiableAt
    exact (hkt.hasDerivAt.pow e).deriv
  have hΩo : IsOpen (K '' ball (0 : ℂ) r) := K.isOpen_image_of_subset_source isOpen_ball hsrc
  have hk0 : k 0 = 0 := by simp [k]
  have hΩ0 : (0 : ℂ) ∈ K '' ball (0 : ℂ) r := ⟨0, mem_ball_self hr, by rw [hK, hk0]⟩
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.1 hΩo 0 hΩ0
  have hzero : ∀ t ∈ ball (0 : ℂ) r, h t = 0 → t = 0 := by
    intro t ht h0
    rw [(hball t (hrsub ht)).2.1] at h0
    have hkt : K t = K 0 := by rw [hK, hk0]; exact pow_eq_zero_iff he.ne' |>.1 h0
    exact K.injOn (hsrc ht) hK0 hkt
  refine ⟨r, hr, min_le_left _ _, δ ^ e, pow_pos hδ e, hzero, fun w hw hwρ ↦ ⟨?_, ?_⟩⟩
  · have hmaps : K '' {t ∈ ball (0 : ℂ) r | h t = w} =
        (Polynomial.nthRootsFinset e w : Set ℂ) := by
      ext s
      simp only [Finset.mem_coe, Polynomial.mem_nthRootsFinset he]
      constructor
      · rintro ⟨t, ⟨ht, htw⟩, rfl⟩
        rw [hK, ← (hball t (hrsub ht)).2.1, htw]
      · intro hs
        have hsδ : ‖s‖ < δ := by
          have : ‖s‖ ^ e < δ ^ e := by rw [← norm_pow, hs]; exact hwρ
          exact lt_of_pow_lt_pow_left₀ e hδ.le this
        obtain ⟨t, ht, rfl⟩ := hδΩ (mem_ball_zero_iff.2 hsδ)
        refine ⟨t, ⟨ht, ?_⟩, rfl⟩
        rw [(hball t (hrsub ht)).2.1, ← hs, hK]
    rw [← Set.InjOn.ncard_image (K.injOn.mono fun t ht ↦ hsrc ht.1), hmaps,
      Set.ncard_coe_finset, b4cov_card_nthRootsFinset he hw]
  · intro t ht htw
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hw (by rw [← htw]; exact (hball 0 (hrsub ht)).2.1.trans (by rw [hk0, zero_pow he.ne']))
    have hkt : k t ≠ 0 := by
      intro hkt
      apply ht0
      exact K.injOn (hsrc ht) hK0 (by rw [hK, hkt, hk0])
    rw [hderiv t ht]
    exact mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 he.ne') (pow_ne_zero _ hkt))
      (hball t (hrsub ht)).2.2.1

/-- **Vanishing order of a coefficient invariant under a rotation**: if `a = m · (a ∘ p)` near
`0` with `p(0) = 0`, `p'(0) = m(0) = ζ` a primitive `n`-th root of unity, then `a` vanishes to
order at least `n - 1`. -/
theorem b4cov_order_ge_of_rel {a m p : ℂ → ℂ} (ha : AnalyticAt ℂ a 0) (hm : AnalyticAt ℂ m 0)
    (hp : AnalyticAt ℂ p 0) (hp0 : p 0 = 0) {ζ : ℂ} (hp' : deriv p 0 = ζ) (hm0 : m 0 = ζ)
    (hrel : ∀ᶠ τ in 𝓝 0, a τ = m τ * a (p τ)) {n : ℕ} (hζ : IsPrimitiveRoot ζ n) :
    (((n - 1 : ℕ) : ℕ∞)) ≤ analyticOrderAt a 0 := by
  cases h : analyticOrderAt a 0 with
  | top => exact le_top
  | coe k =>
    obtain ⟨u, hu, hu0, hau⟩ := ha.analyticOrderAt_eq_natCast.1 h
    have hp1 : (1 : ℕ∞) ≤ analyticOrderAt p 0 := by
      rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl,
        natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hp]
      intro i hi
      rw [Nat.lt_one_iff.1 hi, iteratedDeriv_zero, hp0]
    obtain ⟨q, hq, hpq⟩ := (natCast_le_analyticOrderAt hp (n := 1)).1 hp1
    have hpq' : p =ᶠ[𝓝 0] fun τ ↦ τ * q τ := by
      filter_upwards [hpq] with τ hτ
      rw [hτ, sub_zero, pow_one, smul_eq_mul]
    have hq0 : q 0 = ζ := by
      have hd : HasDerivAt (fun τ ↦ τ * q τ) (q 0) 0 := by
        have := (hasDerivAt_id' (0 : ℂ)).mul hq.differentiableAt.hasDerivAt
        simp only [one_mul, zero_mul, add_zero] at this
        exact this
      rw [← hp', hpq'.deriv_eq, hd.deriv]
    have hau' : ∀ᶠ τ in 𝓝 0, a (p τ) = p τ ^ k * u (p τ) := by
      have := hp.continuousAt.tendsto.eventually (p := fun z ↦ a z = (z - 0) ^ k • u z)
        (by rw [hp0]; exact hau)
      filter_upwards [this] with τ hτ
      rw [hτ, sub_zero, smul_eq_mul]
    let v : ℂ → ℂ := fun τ ↦ m τ * q τ ^ k * u (p τ)
    have hv : AnalyticAt ℂ v 0 :=
      (hm.mul (hq.pow k)).mul ((by rw [hp0]; exact hu : AnalyticAt ℂ u (p 0)).comp hp)
    have hv0 : v 0 = ζ ^ (k + 1) * u 0 := by
      simp only [v, hm0, hq0, hp0]; ring
    have huv : ∀ᶠ τ in 𝓝[≠] (0 : ℂ), u τ = v τ := by
      filter_upwards [nhdsWithin_le_nhds (hrel.and (hau.and (hau'.and hpq'))),
        self_mem_nhdsWithin] with τ ⟨h1, h2, h3, h4⟩ hτ
      have hτk : τ ^ k ≠ 0 := pow_ne_zero _ hτ
      apply mul_left_cancel₀ hτk
      rw [sub_zero, smul_eq_mul] at h2
      have h5 : p τ ^ k = (τ * q τ) ^ k := by rw [h4]
      calc τ ^ k * u τ = a τ := h2.symm
        _ = m τ * (p τ ^ k * u (p τ)) := by rw [h1, h3]
        _ = τ ^ k * v τ := by rw [h5]; simp only [v]; ring
    have hlim : u 0 = v 0 :=
      tendsto_nhds_unique (hu.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        ((hv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (huv.mono fun _ h ↦ h.symm))
    rw [hv0] at hlim
    have hpow : ζ ^ (k + 1) = 1 := by
      have := mul_right_cancel₀ hu0 (hlim.symm.trans (one_mul _).symm)
      exact this
    have hdvd := hζ.dvd_of_pow_eq_one _ hpow
    have : n - 1 ≤ k := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · omega
      · have := Nat.le_of_dvd (Nat.succ_pos k) hdvd
        omega
    exact_mod_cast this

end HodgeLean.Foundations.Program
