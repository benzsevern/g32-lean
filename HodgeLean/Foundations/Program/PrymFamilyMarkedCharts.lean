import HodgeLean.Foundations.Program.PrymFamilyMarkedAtlas

/-! # B6-3g, part 5: charts on the moving fibres

The ingredients of a chart of the filled fibre at a parameter `t` in which the moving projection
`b6t_sphere b t ∘ f` is holomorphic:

* the root chart `v ↦ v (H(vᵉ)/vᵉ)^{1/e}` of a homeomorphism `H` of the plane that fixes `0` and
  moves nearby points by less than their norm (`b63g5_root_chart`);
* the local normal form `ψ ∘ f = ψ (f x) + wᵉ` of a non-constant holomorphic map
  (`b63g5_normal_form`);
* the radial push written in sphere charts (`b63g5_shift`) and its bound: the tent displacement
  is Lipschitz with constant `‖t i - b i‖ / r < 1` near every point, and the push is the identity
  near `∞` (`b63g5_shift_bound`).

HC no distance; AV milestone no distance.
-/

noncomputable section

open Filter Topology Set Complex
open scoped Manifold ContDiff

namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- A principal `e`-th root of a number of norm at most `M ≥ 1` has norm at most `M`. -/
theorem b63g5_norm_root_le {q : ℂ} {M : ℝ} (hM : 1 ≤ M) (hq : ‖q‖ ≤ M) {e : ℕ} (he : e ≠ 0) :
    ‖q ^ ((e : ℂ)⁻¹)‖ ≤ M := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have h1 : (1 : ℝ) ≤ ‖q ^ ((e : ℂ)⁻¹)‖ := hM.trans hlt.le
  have h2 : ‖q ^ ((e : ℂ)⁻¹)‖ ≤ ‖q ^ ((e : ℂ)⁻¹)‖ ^ e := le_self_pow₀ h1 he
  rw [← norm_pow, cpow_nat_inv_pow q he] at h2
  linarith

/-- Principal `e`-th roots of `q` and `q⁻¹` are inverse for `q` in the right half-plane. -/
theorem b63g5_root_mul_root_inv {q : ℂ} (hq : 0 < q.re) {e : ℕ} (he : e ≠ 0) :
    q ^ ((e : ℂ)⁻¹) * q⁻¹ ^ ((e : ℂ)⁻¹) = 1 := by
  have hs : q ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl hq)
  have hq0 : q ≠ 0 := fun h ↦ by simp [h] at hq
  rw [inv_cpow q _ (slitPlane_arg_ne_pi hs)]
  apply mul_inv_cancel₀
  intro h
  have := cpow_nat_inv_pow q he
  rw [h, zero_pow he] at this
  exact hq0 this.symm

/-- A number within `κ < 1` of one lies in the right half-plane. -/
theorem b63g5_re_pos_of_near_one {q : ℂ} {κ : ℝ} (hκ : κ < 1) (hq : ‖q - 1‖ ≤ κ) : 0 < q.re := by
  have := abs_re_le_norm (q - 1)
  rw [sub_re, one_re] at this
  have := (abs_le.1 (this.trans hq)).1
  linarith

/-- **The root chart.** If an open partial homeomorphism `H` of the plane fixes `0` and moves
nearby points by at most `κ < 1` times their norm, then for every `e ≥ 1` there is a chart `K`
about `0` with `K v ^ e = H (v ^ e)`: `K v = v (H(vᵉ)/vᵉ)^{1/e}`, with inverse
`u ↦ u (H⁻¹(uᵉ)/uᵉ)^{1/e}`. -/
theorem b63g5_root_chart (H : OpenPartialHomeomorph ℂ ℂ) (h0 : (0 : ℂ) ∈ H.source)
    (hH0 : H 0 = 0) {κ : ℝ} (hκ : κ < 1) (hb : ∀ᶠ s in 𝓝 (0 : ℂ), ‖H s - s‖ ≤ κ * ‖s‖)
    {e : ℕ} (he : e ≠ 0) :
    ∃ K : OpenPartialHomeomorph ℂ ℂ, (0 : ℂ) ∈ K.source ∧
      ∀ v ∈ K.source, v ^ e ∈ H.source ∧ K v ^ e = H (v ^ e) := by
  set R : ℂ → ℂ := fun q ↦ q ^ ((e : ℂ)⁻¹) with hR
  set Kf : ℂ → ℂ := fun v ↦ v * R (H (v ^ e) / v ^ e) with hKf
  set Kg : ℂ → ℂ := fun u ↦ u * R (H.symm (u ^ e) / u ^ e) with hKg
  have h0t : (0 : ℂ) ∈ H.target := hH0 ▸ H.map_source h0
  have hs0 : H.symm 0 = 0 := by have := H.left_inv h0; rwa [hH0] at this
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 (hb.and (H.open_source.mem_nhds h0))
  have hδb' : ∀ s : ℂ, ‖s‖ < δ → ‖H s - s‖ ≤ κ * ‖s‖ ∧ s ∈ H.source := fun s hs ↦
    hδb (by simpa using hs)
  have hsymm : ∀ᶠ u in 𝓝 (0 : ℂ), u ∈ H.target ∧ ‖H.symm u‖ < δ := by
    have hc := H.continuousAt_symm h0t
    have : ∀ᶠ u in 𝓝 (0 : ℂ), H.symm u ∈ Metric.ball (0 : ℂ) δ :=
      hc.preimage_mem_nhds (by rw [hs0]; exact Metric.ball_mem_nhds 0 hδ)
    filter_upwards [this, H.open_target.mem_nhds h0t] with u hu hut
    exact ⟨hut, by simpa using hu⟩
  obtain ⟨δ', hδ', hδ'b⟩ := Metric.eventually_nhds_iff.1 hsymm
  have hδ'b' : ∀ u : ℂ, ‖u‖ < δ' → u ∈ H.target ∧ ‖H.symm u‖ < δ := fun u hu ↦
    hδ'b (by simpa using hu)
  -- the powers
  have hKf_pow : ∀ v, Kf v ^ e = H (v ^ e) := by
    intro v
    by_cases hv : v = 0
    · simp [hKf, hv, zero_pow he, hH0]
    · have hve : v ^ e ≠ 0 := pow_ne_zero _ hv
      simp only [hKf, hR, mul_pow, cpow_nat_inv_pow _ he]
      field_simp
  have hKg_pow : ∀ u, Kg u ^ e = H.symm (u ^ e) := by
    intro u
    by_cases hu : u = 0
    · simp [hKg, hu, zero_pow he, hs0]
    · have hue : u ^ e ≠ 0 := pow_ne_zero _ hu
      simp only [hKg, hR, mul_pow, cpow_nat_inv_pow _ he]
      field_simp
  -- the quotients lie near one
  have hq : ∀ v, ‖v ^ e‖ < δ → v ≠ 0 → ‖H (v ^ e) / v ^ e - 1‖ ≤ κ := by
    intro v hv hv0
    have hve : v ^ e ≠ 0 := pow_ne_zero _ hv0
    have hn : 0 < ‖v ^ e‖ := norm_pos_iff.2 hve
    rw [show H (v ^ e) / v ^ e - 1 = (H (v ^ e) - v ^ e) / v ^ e by field_simp, norm_div,
      div_le_iff₀ hn]
    exact (hδb' _ hv).1
  have hq' : ∀ u, ‖u ^ e‖ < δ' → u ≠ 0 → ‖(H.symm (u ^ e) / u ^ e)⁻¹ - 1‖ ≤ κ := by
    intro u hu hu0
    have hue : u ^ e ≠ 0 := pow_ne_zero _ hu0
    obtain ⟨hut, hsδ⟩ := hδ'b' _ hu
    set s := H.symm (u ^ e)
    have hHs : H s = u ^ e := H.right_inv hut
    have hs0' : s ≠ 0 := fun h ↦ hue (by rw [← hHs, h, hH0])
    have hn : 0 < ‖s‖ := norm_pos_iff.2 hs0'
    rw [inv_div, show u ^ e / s - 1 = (H s - s) / s by rw [hHs]; field_simp, norm_div,
      div_le_iff₀ hn]
    exact (hδb' _ hsδ).1
  -- inverse identities
  have hleft : ∀ v, ‖v ^ e‖ < δ → Kg (Kf v) = v := by
    intro v hv
    by_cases hv0 : v = 0
    · simp [hKf, hKg, hv0]
    have hre := b63g5_re_pos_of_near_one hκ (hq v hv hv0)
    have hsrc := (hδb' _ hv).2
    have : Kg (Kf v) = v * (R (H (v ^ e) / v ^ e) * R (H (v ^ e) / v ^ e)⁻¹) := by
      simp only [hKg]
      rw [hKf_pow, H.left_inv hsrc, inv_div]
      simp only [hKf]
      ring
    rw [this, hR, b63g5_root_mul_root_inv hre he, mul_one]
  have hright : ∀ u, ‖u ^ e‖ < δ' → Kf (Kg u) = u := by
    intro u hu
    by_cases hu0 : u = 0
    · simp [hKf, hKg, hu0]
    have hre := b63g5_re_pos_of_near_one hκ (hq' u hu hu0)
    have hre' : 0 < (H.symm (u ^ e) / u ^ e).re := by
      have h := hre
      rw [inv_re] at h
      exact (div_pos_iff_of_pos_right (normSq_pos.2 fun h0 ↦ by simp [h0] at h)).1 h
    obtain ⟨hut, -⟩ := hδ'b' _ hu
    have : Kf (Kg u) = u * (R (H.symm (u ^ e) / u ^ e) * R (H.symm (u ^ e) / u ^ e)⁻¹) := by
      simp only [hKf]
      rw [hKg_pow, H.right_inv hut, inv_div]
      simp only [hKg]
      ring
    rw [this, hR, b63g5_root_mul_root_inv hre' he, mul_one]
  -- norm bounds
  have hKf_bd : ∀ v, ‖v ^ e‖ < δ → ‖Kf v‖ ≤ 2 * ‖v‖ := by
    intro v hv
    by_cases hv0 : v = 0
    · simp [hKf, hv0]
    have h1 := hq v hv hv0
    have h2 : ‖H (v ^ e) / v ^ e‖ ≤ 2 := by
      have := norm_le_norm_add_norm_sub' (H (v ^ e) / v ^ e) 1
      rw [norm_one] at this
      linarith
    simp only [hKf, norm_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (b63g5_norm_root_le (by norm_num) h2 he) (norm_nonneg _)
  set M : ℝ := max 1 (1 - κ)⁻¹ with hM
  have hKg_bd : ∀ u, ‖u ^ e‖ < δ' → ‖Kg u‖ ≤ M * ‖u‖ := by
    intro u hu
    by_cases hu0 : u = 0
    · simp [hKg, hu0]
    have h1 := hq' u hu hu0
    have hpos : 0 < 1 - κ := by linarith
    have h2 : 1 - κ ≤ ‖(H.symm (u ^ e) / u ^ e)⁻¹‖ := by
      have := norm_sub_norm_le (1 : ℂ) ((H.symm (u ^ e) / u ^ e)⁻¹)
      rw [norm_one, norm_sub_rev] at this
      linarith
    have h3 : ‖H.symm (u ^ e) / u ^ e‖ ≤ M := by
      rw [norm_inv] at h2
      have h4 : 0 < ‖H.symm (u ^ e) / u ^ e‖ := by
        by_contra h5
        have h6 : ‖H.symm (u ^ e) / u ^ e‖ = 0 := le_antisymm (not_lt.1 h5) (norm_nonneg _)
        rw [h6, inv_zero] at h2
        linarith
      have : ‖H.symm (u ^ e) / u ^ e‖ ≤ (1 - κ)⁻¹ := by
        rw [le_inv_comm₀ h4 hpos]; exact h2
      exact this.trans (le_max_right _ _)
    simp only [hKg, norm_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (b63g5_norm_root_le (le_max_left _ _) h3 he) (norm_nonneg _)
  -- continuity
  have hpowc : Continuous fun v : ℂ ↦ ‖v ^ e‖ := continuous_norm.comp (continuous_pow e)
  have hKf_cont : ∀ v, ‖v ^ e‖ < δ → ContinuousAt Kf v := by
    intro v hv
    by_cases hv0 : v = 0
    · subst hv0
      have hK0 : Kf 0 = 0 := by simp [hKf]
      rw [ContinuousAt, hK0]
      refine squeeze_zero_norm' (a := fun w : ℂ ↦ 2 * ‖w‖) ?_ ?_
      · filter_upwards [(isOpen_lt hpowc continuous_const).mem_nhds hv] with w hw
        exact hKf_bd w hw
      · have hc : Continuous (fun w : ℂ ↦ (2 : ℝ) * ‖w‖) := continuous_const.mul continuous_norm
        simpa using hc.tendsto 0
    have hve : v ^ e ≠ 0 := pow_ne_zero _ hv0
    have hsrc := (hδb' _ hv).2
    have hslit : H (v ^ e) / v ^ e ∈ slitPlane :=
      mem_slitPlane_iff.2 (Or.inl (b63g5_re_pos_of_near_one hκ (hq v hv hv0)))
    have h1 : ContinuousAt (fun w : ℂ ↦ H (w ^ e)) v :=
      (H.continuousAt hsrc).comp (f := fun w : ℂ ↦ w ^ e) (continuous_pow e).continuousAt
    have h2 : ContinuousAt (fun w : ℂ ↦ H (w ^ e) / w ^ e) v :=
      h1.div (continuous_pow e).continuousAt hve
    exact continuousAt_id.mul
      ((continuousAt_cpow_const hslit).comp (f := fun w : ℂ ↦ H (w ^ e) / w ^ e) h2)
  have hKg_cont : ∀ u, ‖u ^ e‖ < δ' → ContinuousAt Kg u := by
    intro u hu
    by_cases hu0 : u = 0
    · subst hu0
      have hK0 : Kg 0 = 0 := by simp [hKg]
      rw [ContinuousAt, hK0]
      refine squeeze_zero_norm' (a := fun w : ℂ ↦ M * ‖w‖) ?_ ?_
      · filter_upwards [(isOpen_lt hpowc continuous_const).mem_nhds hu] with w hw
        exact hKg_bd w hw
      · have hc : Continuous (fun w : ℂ ↦ M * ‖w‖) := continuous_const.mul continuous_norm
        simpa using hc.tendsto 0
    have hue : u ^ e ≠ 0 := pow_ne_zero _ hu0
    have hut := (hδ'b' _ hu).1
    have hre := b63g5_re_pos_of_near_one hκ (hq' u hu hu0)
    have hre' : 0 < (H.symm (u ^ e) / u ^ e).re := by
      have h := hre
      rw [inv_re] at h
      exact (div_pos_iff_of_pos_right (normSq_pos.2 fun h0 ↦ by simp [h0] at h)).1 h
    have hslit : H.symm (u ^ e) / u ^ e ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl hre')
    have h1 : ContinuousAt (fun w : ℂ ↦ H.symm (w ^ e)) u :=
      (H.continuousAt_symm hut).comp (f := fun w : ℂ ↦ w ^ e) (continuous_pow e).continuousAt
    have h2 : ContinuousAt (fun w : ℂ ↦ H.symm (w ^ e) / w ^ e) u :=
      h1.div (continuous_pow e).continuousAt hue
    exact continuousAt_id.mul
      ((continuousAt_cpow_const hslit).comp (f := fun w : ℂ ↦ H.symm (w ^ e) / w ^ e) h2)
  -- the chart
  set S : Set ℂ := {v | ‖v ^ e‖ < δ ∧ (1 + κ) * ‖v ^ e‖ < δ'} with hS
  set B : Set ℂ := {u | ‖u ^ e‖ < δ'} with hB
  have hSo : IsOpen S :=
    (isOpen_lt hpowc continuous_const).inter (isOpen_lt (continuous_const.mul hpowc) continuous_const)
  have hBo : IsOpen B := isOpen_lt hpowc continuous_const
  have hKgB : ContinuousOn Kg B := fun u hu ↦ (hKg_cont u hu).continuousWithinAt
  have hKfB : ∀ v ∈ S, Kf v ∈ B := by
    intro v hv
    show ‖Kf v ^ e‖ < δ'
    rw [hKf_pow]
    have h1 := (hδb' _ hv.1).1
    have h2 : ‖H (v ^ e)‖ ≤ (1 + κ) * ‖v ^ e‖ := by
      have := norm_le_norm_add_norm_sub' (H (v ^ e)) (v ^ e)
      linarith
    exact h2.trans_lt hv.2
  let K : OpenPartialHomeomorph ℂ ℂ :=
    { toFun := Kf
      invFun := Kg
      source := S
      target := B ∩ Kg ⁻¹' S
      map_source' := fun v hv ↦ ⟨hKfB v hv, by rw [mem_preimage, hleft v hv.1]; exact hv⟩
      map_target' := fun u hu ↦ hu.2
      left_inv' := fun v hv ↦ hleft v hv.1
      right_inv' := fun u hu ↦ hright u hu.1
      open_source := hSo
      open_target := hKgB.isOpen_inter_preimage hBo hSo
      continuousOn_toFun := fun v hv ↦ (hKf_cont v hv.1).continuousWithinAt
      continuousOn_invFun := fun u hu ↦ (hKg_cont u hu.1).continuousWithinAt }
  refine ⟨K, ?_, fun v hv ↦ ⟨(hδb' _ hv.1).2, hKf_pow v⟩⟩
  show ‖(0 : ℂ) ^ e‖ < δ ∧ (1 + κ) * ‖(0 : ℂ) ^ e‖ < δ'
  simp [zero_pow he, hδ, hδ']

/-- **Local normal form.** A non-constant holomorphic map `f` from a connected Riemann surface to
the sphere is, near each point `x`, of the form `ψ ∘ f = ψ (f x) + wᵉ` for a holomorphic chart
`w` at `x` and the sphere chart `ψ` at `f x`, with `e ≥ 1`. -/
theorem b63g5_normal_form {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [ConnectedSpace C] (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hnc : ∃ a b, f a ≠ f b) (x : C) :
    ∃ (e : ℕ) (w : OpenPartialHomeomorph C ℂ), e ≠ 0 ∧ x ∈ w.source ∧ w x = 0 ∧
      ∀ y ∈ w.source, f y ∈ (chartAt ℂ (f x)).source ∧
        chartAt ℂ (f x) (f y) = chartAt ℂ (f x) (f x) + w y ^ e := by
  set φ := chartAt ℂ x
  set ψ := chartAt ℂ (f x)
  set z₀ := φ x
  have hx : x ∈ φ.source := mem_chart_source ℂ x
  have hz₀ : z₀ ∈ φ.target := φ.map_source hx
  have hfφ : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (f ∘ φ.symm) φ.target :=
    hf.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(ℂ, ℂ)))
  have hfz₀ : (f ∘ φ.symm) z₀ = f x := by simp [z₀, φ.left_inv hx]
  set g : ℂ → ℂ := ψ ∘ (f ∘ φ.symm)
  have hgz₀ : g z₀ = ψ (f x) := by
    show ψ ((f ∘ φ.symm) z₀) = _
    rw [hfz₀]
  have hgan : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ g z :=
    b63g5_analyticAt_chart_comp φ.open_target hfφ hz₀ (f x)
      (by rw [hfz₀]; exact mem_chart_source ℂ (f x))
  have hsrc : ∀ᶠ z in 𝓝 z₀, (f ∘ φ.symm) z ∈ ψ.source :=
    (hfφ.continuousOn.continuousAt (φ.open_target.mem_nhds hz₀)).preimage_mem_nhds
      (ψ.open_source.mem_nhds (by rw [hfz₀]; exact mem_chart_source ℂ (f x)))
  -- `g - g z₀` does not vanish identically near `z₀`
  have hG : AnalyticAt ℂ (fun z ↦ g z - g z₀) z₀ := hgan.self_of_nhds.sub analyticAt_const
  have hGnz : ¬ ∀ᶠ z in 𝓝 z₀, g z - g z₀ = 0 := by
    intro h0
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    refine b4cov_const_of_eventuallyConst f hf x ?_ a b
    have h1 : ∀ᶠ z in 𝓝 z₀, f (φ.symm z) = f x := by
      filter_upwards [h0, hsrc, φ.open_target.mem_nhds hz₀] with z hz hzs hzt
      have hψ : ψ (f (φ.symm z)) = ψ (f x) := by
        have := sub_eq_zero.1 hz
        rw [hgz₀] at this
        exact this
      exact ψ.injOn hzs (mem_chart_source ℂ (f x)) hψ
    have h2 := (φ.continuousAt hx).preimage_mem_nhds h1
    filter_upwards [h2, φ.open_source.mem_nhds hx] with y hy hys
    simpa [φ.left_inv hys] using hy
  obtain ⟨n, u, hu, hu0, hGu⟩ := hG.exists_eventuallyEq_pow_smul_nonzero_iff.2 hGnz
  have hn : n ≠ 0 := by
    rintro rfl
    have := hGu.self_of_nhds
    simp only [sub_self, pow_zero, one_smul] at this
    exact hu0 this.symm
  set α : ℂ := u z₀ ^ ((n : ℂ)⁻¹)
  have hα : α ^ n = u z₀ := cpow_nat_inv_pow _ hn
  have hα0 : α ≠ 0 := fun h ↦ hu0 (by rw [← hα, h, zero_pow hn])
  set v : ℂ → ℂ := fun z ↦ (z - z₀) * (α * (u z / u z₀) ^ ((n : ℂ)⁻¹))
  have hslit : u z₀ / u z₀ ∈ slitPlane := by
    rw [div_self hu0]; exact one_mem_slitPlane
  have hcan : AnalyticAt ℂ (fun z ↦ α * (u z / u z₀) ^ ((n : ℂ)⁻¹)) z₀ :=
    analyticAt_const.mul ((hu.div analyticAt_const hu0).cpow analyticAt_const hslit)
  have hvan : AnalyticAt ℂ v z₀ := (analyticAt_id.sub analyticAt_const).mul hcan
  have hc₀ : α * (u z₀ / u z₀) ^ ((n : ℂ)⁻¹) = α := by
    rw [div_self hu0, one_cpow, mul_one]
  have hvd : HasDerivAt v α z₀ := by
    have h1 : HasDerivAt (fun z : ℂ ↦ z - z₀) 1 z₀ := (hasDerivAt_id z₀).sub_const z₀
    have h2 : HasDerivAt v (1 * (α * (u z₀ / u z₀) ^ ((n : ℂ)⁻¹)) + (z₀ - z₀) *
        deriv (fun z ↦ α * (u z / u z₀) ^ ((n : ℂ)⁻¹)) z₀) z₀ :=
      h1.mul hcan.differentiableAt.hasDerivAt
    simpa [hc₀] using h2
  have hvs : HasStrictDerivAt v α z₀ := by
    have := hvan.hasStrictDerivAt
    rwa [hvd.deriv] at this
  have hvpow : ∀ᶠ z in 𝓝 z₀, g z - g z₀ = v z ^ n := by
    filter_upwards [hGu] with z hz
    rw [hz, smul_eq_mul]
    simp only [v, mul_pow, cpow_nat_inv_pow _ hn, hα]
    field_simp
  have hfd := hvs.hasStrictFDerivAt_equiv hα0
  set V := hfd.toOpenPartialHomeomorph v
  have hVv : (V : ℂ → ℂ) = v := hfd.toOpenPartialHomeomorph_coe
  obtain ⟨O, hOsub, hOo, hz₀O⟩ := mem_nhds_iff.1 (hvpow.and (hsrc.and (φ.open_target.mem_nhds hz₀)))
  let w : OpenPartialHomeomorph C ℂ := φ.trans (V.restrOpen O hOo)
  have hwapp : ∀ y, w y = v (φ y) := fun y ↦ by
    simp [w, OpenPartialHomeomorph.trans_apply, hVv]
  refine ⟨n, w, hn, ?_, ?_, fun y hy ↦ ?_⟩
  · simp only [w, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hx, hfd.mem_toOpenPartialHomeomorph_source, hz₀O⟩
  · rw [hwapp]; simp [v, z₀]
  · simp only [w, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source,
      mem_inter_iff, mem_preimage] at hy
    obtain ⟨hys, -, hyO⟩ := hy
    obtain ⟨h1, h2, -⟩ := hOsub hyO
    have hfy : (f ∘ φ.symm) (φ y) = f y := by simp [φ.left_inv hys]
    rw [hfy] at h2
    refine ⟨h2, ?_⟩
    rw [hwapp, ← h1, hgz₀, add_sub_cancel]
    show ψ (f y) = ψ ((f ∘ φ.symm) (φ y))
    rw [hfy]

/-- The tent weights are `1 / r`-Lipschitz. -/
theorem b63g5_tent_lipschitz (c : ℂ) {r : ℝ} (hr : 0 < r) (z z' : ℂ) :
    |max 0 (1 - dist z c / r) - max 0 (1 - dist z' c / r)| ≤ ‖z - z'‖ / r := by
  have hmax := abs_max_sub_max_le_max (0 : ℝ) (1 - dist z c / r) 0 (1 - dist z' c / r)
  have h2 : |(1 - dist z c / r) - (1 - dist z' c / r)| = |dist z' c - dist z c| / r := by
    rw [show (1 - dist z c / r) - (1 - dist z' c / r) = (dist z' c - dist z c) / r by ring,
      abs_div, abs_of_pos hr]
  have h3 : |dist z' c - dist z c| ≤ ‖z - z'‖ := by
    rw [← dist_eq_norm, dist_comm z z']
    exact abs_dist_sub_le z' z c
  have h4 : |(1 - dist z c / r) - (1 - dist z' c / r)| ≤ ‖z - z'‖ / r := by
    rw [h2]; exact div_le_div_of_nonneg_right h3 hr.le
  calc _ ≤ max |(0 : ℝ) - 0| |(1 - dist z c / r) - (1 - dist z' c / r)| := hmax
    _ ≤ ‖z - z'‖ / r := max_le (by simp; positivity) h4

/-- A tent weight vanishes outside its disc and boundary circle. -/
theorem b63g5_tent_eq_zero (c : ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∉ Metric.closedBall c r) : max 0 (1 - dist z c / r) = 0 := by
  have hd : r < dist z c := by simpa [Metric.mem_closedBall, not_le] using hz
  have : 1 - dist z c / r < 0 := by
    rw [sub_neg, one_lt_div hr]; exact hd
  exact max_eq_left this.le

/-- **The radial push moves nearby points by less than their distance.** Near every point of
the plane, the displacement of `b6t_plane b t` is `κ`-Lipschitz with `κ < 1`: only one tent can be
nonzero near the point, and its displacement vector is shorter than the radius. -/
theorem b63g5_plane_bound (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ)
    (ht : t ∈ b6t_polydisc b) (y : ℂ) :
    ∃ κ < 1, ∀ᶠ s in 𝓝 (0 : ℂ),
      ‖b6t_plane b t (y + s) - b6t_plane b t y - s‖ ≤ κ * ‖s‖ := by
  obtain ⟨hr, -, hdisj⟩ := b6t_discs b hb
  set r := b6t_radius b
  -- an index whose disc is the only one that can meet a neighbourhood of `y`
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin 10, ∀ j, j ≠ i₀ → y ∉ Metric.closedBall (b j) r := by
    by_cases h : ∃ i, y ∈ Metric.closedBall (b i) r
    · obtain ⟨i, hi⟩ := h
      exact ⟨i, fun j hj hyj ↦ Set.disjoint_left.1 (hdisj hj) hyj hi⟩
    · push Not at h
      exact ⟨0, fun j _ ↦ h j⟩
  have hev : ∀ᶠ z in 𝓝 y, ∀ j, j ≠ i₀ → z ∉ Metric.closedBall (b j) r := by
    refine Filter.eventually_all.2 fun j ↦ ?_
    by_cases hj : j = i₀
    · exact Filter.Eventually.of_forall fun _ h ↦ absurd hj h
    · filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds (hi₀ j hj)] with z hz _
      exact hz
  have htend : Tendsto (fun s : ℂ ↦ y + s) (𝓝 0) (𝓝 y) := by
    have hc : Continuous (fun s : ℂ ↦ y + s) := continuous_const.add continuous_id
    simpa using hc.tendsto (0 : ℂ)
  refine ⟨‖t i₀ - b i₀‖ / r, ?_, ?_⟩
  · rw [div_lt_one hr]
    simpa [dist_eq_norm] using ht i₀
  filter_upwards [htend.eventually hev] with s hs
  have hsum : b6t_plane b t (y + s) - b6t_plane b t y - s =
      ∑ j : Fin 10, (max 0 (1 - dist (y + s) (b j) / r) - max 0 (1 - dist y (b j) / r)) •
        (t j - b j) := by
    simp only [b6t_plane, sub_smul, Finset.sum_sub_distrib]
    ring
  rw [hsum, Finset.sum_eq_single i₀]
  · rw [norm_smul, Real.norm_eq_abs]
    calc _ ≤ ‖(y + s) - y‖ / r * ‖t i₀ - b i₀‖ :=
          mul_le_mul_of_nonneg_right (b63g5_tent_lipschitz _ hr _ _) (norm_nonneg _)
      _ = ‖t i₀ - b i₀‖ / r * ‖s‖ := by rw [add_sub_cancel_left]; ring
  · intro j _ hj
    rw [b63g5_tent_eq_zero _ hr (hs j hj), b63g5_tent_eq_zero _ hr (hi₀ j hj), sub_self,
      zero_smul]
  · intro h; exact absurd (Finset.mem_univ i₀) h

/-- The sphere homeomorphism `E` near `p`, written in the sphere charts at `p` and `E p` and
centred at `0`: `s ↦ ψ₁ (E (ψ₀⁻¹ (ψ₀ p + s))) - ψ₁ (E p)`. -/
def b63g5_shift (E : OnePoint ℂ ≃ₜ OnePoint ℂ) (p : OnePoint ℂ) : OpenPartialHomeomorph ℂ ℂ :=
  (Homeomorph.addLeft (chartAt ℂ p p)).toOpenPartialHomeomorph.trans
    ((chartAt ℂ p).symm.trans (E.toOpenPartialHomeomorph.trans ((chartAt ℂ (E p)).trans
      (Homeomorph.addRight (-(chartAt ℂ (E p) (E p)))).toOpenPartialHomeomorph)))

theorem b63g5_shift_apply (E : OnePoint ℂ ≃ₜ OnePoint ℂ) (p : OnePoint ℂ) (s : ℂ) :
    b63g5_shift E p s =
      chartAt ℂ (E p) (E ((chartAt ℂ p).symm (chartAt ℂ p p + s))) - chartAt ℂ (E p) (E p) := by
  simp [b63g5_shift, sub_eq_add_neg]

theorem b63g5_shift_source (E : OnePoint ℂ ≃ₜ OnePoint ℂ) (p : OnePoint ℂ) {s : ℂ}
    (hs : s ∈ (b63g5_shift E p).source) :
    chartAt ℂ p p + s ∈ (chartAt ℂ p).target ∧
      E ((chartAt ℂ p).symm (chartAt ℂ p p + s)) ∈ (chartAt ℂ (E p)).source := by
  simp only [b63g5_shift, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    OpenPartialHomeomorph.symm_source, univ_inter, mem_preimage, mem_inter_iff,
    Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.coe_addLeft] at hs
  exact ⟨hs.1, hs.2.1⟩

theorem b63g5_shift_zero (E : OnePoint ℂ ≃ₜ OnePoint ℂ) (p : OnePoint ℂ) :
    (0 : ℂ) ∈ (b63g5_shift E p).source ∧ b63g5_shift E p 0 = 0 := by
  have hp := mem_chart_source ℂ p
  refine ⟨?_, ?_⟩
  · simp only [b63g5_shift, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, OpenPartialHomeomorph.symm_source, univ_inter,
      mem_preimage, mem_inter_iff, Homeomorph.toOpenPartialHomeomorph_apply,
      Homeomorph.coe_addLeft, add_zero]
    refine ⟨(chartAt ℂ p).map_source hp, ?_⟩
    rw [(chartAt ℂ p).left_inv hp]
    exact ⟨mem_chart_source ℂ (E p), mem_univ _⟩
  · rw [b63g5_shift_apply, add_zero, (chartAt ℂ p).left_inv hp, sub_self]

/-- **The shift nearly fixes small vectors.** For the radial push of a parameter of the polydisc,
the shift at every point of the sphere moves nearby points by at most `κ < 1` times their norm. -/
theorem b63g5_shift_bound (b : Fin 10 → ℂ) (hb : b ∈ b6_chart) (t : Fin 10 → ℂ)
    (ht : t ∈ b6t_polydisc b) (E : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hE : ∀ x, E x = b6t_sphere b t x) (p : OnePoint ℂ) :
    ∃ κ < 1, ∀ᶠ s in 𝓝 (0 : ℂ), ‖b63g5_shift E p s - s‖ ≤ κ * ‖s‖ := by
  induction p using OnePoint.rec with
  | infty =>
    have hEi : E OnePoint.infty = OnePoint.infty := by rw [hE]; rfl
    have hfix := (b6t_fixed b hb t ht).2.2.2
    obtain ⟨hr, -, -⟩ := b6t_discs b hb
    set R : ℝ := ∑ i : Fin 10, (‖b i‖ + b6t_radius b) + 1
    have hR : ∀ i, ‖b i‖ + b6t_radius b < R := by
      intro i
      have := Finset.single_le_sum (f := fun i : Fin 10 ↦ ‖b i‖ + b6t_radius b)
        (fun j _ ↦ by positivity) (Finset.mem_univ i)
      linarith
    have hR0 : 0 < R := lt_of_le_of_lt (by positivity) (hR 0)
    refine ⟨0, zero_lt_one, ?_⟩
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (inv_pos.2 hR0)] with s hs
    rw [b63g5_shift_apply, hEi, b4cov_chartAt_infty]
    have h0 : b4cov_chartInf OnePoint.infty = 0 := by
      rw [b4cov_chartInf_apply, b4cov_sphInv_infty, b4cov_chart0_coe]
    rw [h0, zero_add, sub_zero]
    by_cases hs0 : s = 0
    · subst hs0
      rw [b4cov_chartInf_symm, b4cov_sphInv_zero, hEi, h0]; simp
    have hsR : R < ‖s⁻¹‖ := by
      rw [norm_inv]
      rw [mem_ball_zero_iff] at hs
      exact (lt_inv_comm₀ (norm_pos_iff.2 hs0) hR0).1 hs
    have hout : ((s⁻¹ : ℂ) : OnePoint ℂ) ∉ ⋃ i : Fin 10, ((↑) : ℂ → OnePoint ℂ) ''
        Metric.closedBall (b i) (b6t_radius b) := by
      simp only [mem_iUnion, mem_image, not_exists, not_and]
      intro i z hz hzs
      have hzs' : z = s⁻¹ := OnePoint.coe_injective hzs
      subst hzs'
      have hd := Metric.mem_closedBall.1 hz
      have : ‖s⁻¹‖ ≤ ‖b i‖ + b6t_radius b := by
        have := norm_le_norm_add_norm_sub' (s⁻¹) (b i)
        rw [← dist_eq_norm] at this
        linarith
      linarith [hR i]
    rw [b4cov_chartInf_symm, b4cov_sphInv_coe hs0, hE, hfix _ hout, b4cov_chartInf_apply,
      b4cov_sphInv_coe (inv_ne_zero hs0), inv_inv, b4cov_chart0_coe, sub_self, norm_zero,
      zero_mul]
  | coe y =>
    obtain ⟨κ, hκ, hev⟩ := b63g5_plane_bound b hb t ht y
    refine ⟨κ, hκ, ?_⟩
    filter_upwards [hev] with s hs
    have hEy : ∀ z : ℂ, E (z : OnePoint ℂ) = ((b6t_plane b t z : ℂ) : OnePoint ℂ) := fun z ↦ by
      rw [hE]; rfl
    rw [b63g5_shift_apply, hEy, b4cov_chartAt_coe, b4cov_chartAt_coe, b4cov_chart0_coe,
      b4cov_chart0_symm, hEy, b4cov_chart0_coe, b4cov_chart0_coe]
    exact hs

end HodgeLean.Foundations.Program
