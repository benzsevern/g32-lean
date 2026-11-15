import HodgeLean.Foundations.Program.CurveJacobianAPlumbing

/-! # Track B3, lane A: crossings of transverse loops

A nonzero orientation `b3_orient v w` makes `v`, `w` independent over `ℝ`, so at a transverse
crossing the map `(s, t) ↦ φ(γ s) - φ(δ t)` has injective derivative and the crossing is isolated;
on a Hausdorff surface the crossings in `[0, 1]²` form a compact discrete set, hence a finite one.
-/

noncomputable section

open Manifold Filter Topology Set
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section Crossings

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The orientation form is `ℝ`-linear in the second argument. -/
theorem b3A_orient_smul_right (v w : E) (r : ℝ) :
    b3_orient E v ((r : ℂ) • w) = r * b3_orient E v w := by
  simp only [b3_orient, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re]
  ring

/-- The orientation of `(v, v)` is zero. -/
theorem b3A_orient_self (v : E) : b3_orient E v v = 0 := by
  simp only [b3_orient]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Vectors with nonzero orientation are `ℝ`-independent. -/
theorem b3A_indep_of_orient (v w : E) (h : b3_orient E v w ≠ 0) (a b : ℝ)
    (hab : a • v + b • w = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    simp only [zero_smul, add_zero, smul_eq_zero] at hab
    rcases hab with ha | hv
    · exact ⟨ha, rfl⟩
    · subst hv
      simp [b3_orient] at h
  · exfalso
    have h1 : b • w = -(a • v) := eq_neg_of_add_eq_zero_right hab
    have hw' : w = (-a / b) • v := by
      calc w = b⁻¹ • (b • w) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = (-a / b) • v := by rw [h1, smul_neg, smul_smul, neg_div, neg_smul, div_eq_inv_mul]
    have hw : w = ((-a / b : ℝ) : ℂ) • v := by rw [Complex.coe_smul]; exact hw'
    apply h
    rw [hw, b3A_orient_smul_right, b3A_orient_self, mul_zero]

variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

omit [FiniteDimensional ℂ E] in
/-- A `C¹` path read in the chart at its own point has derivative its velocity. -/
theorem b3A_chart_hasDerivAt_self (γ : ℝ → C) (s : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ s) :
    HasDerivAt (chartAt E (γ s) ∘ γ) (b3A_vel (E := E) γ s) s := by
  obtain ⟨hd, he⟩ := b3A_chart_comp γ s hγ (γ s) (mem_chart_source E _)
  have hid : fderiv ℂ (chartAt E (γ s) ∘ (chartAt E (γ s)).symm) (chartAt E (γ s) (γ s)) =
      ContinuousLinearMap.id ℂ E := by
    have : (chartAt E (γ s) ∘ (chartAt E (γ s)).symm) =ᶠ[𝓝 (chartAt E (γ s) (γ s))] id := by
      filter_upwards [(chartAt E (γ s)).open_target.mem_nhds
        ((chartAt E (γ s)).map_source (mem_chart_source E _))] with y hy
      exact (chartAt E (γ s)).right_inv hy
    rw [this.fderiv_eq, fderiv_id]
  have := (hd.differentiableAt one_ne_zero).hasFDerivAt.hasDerivAt
  rw [he, hid] at this
  exact this

/-- **Transverse crossings are isolated.** -/
theorem b3A_crossing_isolated (γ δ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    (hδ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 δ) (s₀ t₀ : ℝ) (h : γ s₀ = δ t₀)
    (ho : b3_orient E (b3_velocity E C γ s₀) (b3_velocity E C δ t₀) ≠ 0) :
    ∀ᶠ p in 𝓝[≠] (s₀, t₀), γ p.1 ≠ δ p.2 := by
  set x := γ s₀
  have hc := b3A_chart_hasDerivAt_self γ s₀ (hγ s₀)
  have hd := b3A_chart_hasDerivAt_self δ t₀ (hδ t₀)
  rw [← h] at hd
  set v := b3A_vel (E := E) γ s₀
  set w := b3A_vel (E := E) (C := C) δ t₀
  set L : ℝ × ℝ →L[ℝ] E :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight v).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) -
    ((ContinuousLinearMap.id ℝ ℝ).smulRight w).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have h1 : HasFDerivAt (fun p : ℝ × ℝ ↦ chartAt E x (γ p.1))
      (((ContinuousLinearMap.id ℝ ℝ).smulRight v).comp (ContinuousLinearMap.fst ℝ ℝ ℝ))
      (s₀, t₀) :=
    HasFDerivAt.comp (g := chartAt E x ∘ γ) (f := Prod.fst) (s₀, t₀) hc.hasFDerivAt
      (hasFDerivAt_fst : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) _ (s₀, t₀))
  have h2 : HasFDerivAt (fun p : ℝ × ℝ ↦ chartAt E x (δ p.2))
      (((ContinuousLinearMap.id ℝ ℝ).smulRight w).comp (ContinuousLinearMap.snd ℝ ℝ ℝ))
      (s₀, t₀) :=
    HasFDerivAt.comp (g := chartAt E x ∘ δ) (f := Prod.snd) (s₀, t₀) hd.hasFDerivAt
      (hasFDerivAt_snd : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) _ (s₀, t₀))
  have hF : HasFDerivAt (fun p : ℝ × ℝ ↦ chartAt E x (γ p.1) - chartAt E x (δ p.2)) L (s₀, t₀) :=
    h1.sub h2
  have hL : LinearMap.ker (L : ℝ × ℝ →ₗ[ℝ] E) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ hab
    have hab' : a • v + (-b) • w = 0 := by
      simpa [L, sub_eq_add_neg, neg_smul] using hab
    obtain ⟨ha, hb⟩ := b3A_indep_of_orient v w ho a (-b) hab'
    simp [ha, neg_eq_zero.1 hb]
  obtain ⟨K, -, hK⟩ := (L : ℝ × ℝ →ₗ[ℝ] E).exists_antilipschitzWith hL
  have hne := hF.eventually_ne (c := chartAt E x (γ s₀) - chartAt E x (δ t₀)) ⟨K, hK⟩
  have hsrc : ∀ᶠ p in 𝓝 (s₀, t₀), γ p.1 ∈ (chartAt E x).source ∧ δ p.2 ∈ (chartAt E x).source := by
    have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (s₀, t₀), γ p.1 ∈ (chartAt E x).source :=
      (hγ.continuous.comp continuous_fst).continuousAt.preimage_mem_nhds
        ((chartAt E x).open_source.mem_nhds (mem_chart_source E x))
    have h2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (s₀, t₀), δ p.2 ∈ (chartAt E x).source :=
      (hδ.continuous.comp continuous_snd).continuousAt.preimage_mem_nhds
        ((chartAt E x).open_source.mem_nhds (by
          show δ t₀ ∈ _
          rw [← h]
          exact mem_chart_source E x))
    exact h1.and h2
  filter_upwards [hne, nhdsWithin_le_nhds hsrc] with p hp _ hpq
  apply hp
  rw [hpq, ← h, sub_self, sub_self]

/-- **Transverse loops on a Hausdorff surface cross finitely often.** -/
theorem b3A_crossings_finite [T2Space C] (γ δ : b3_SmoothLoop E C) (h : b3_Transverse E γ δ) :
    (b3_crossings E γ δ).Finite := by
  set S := (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ {p : ℝ × ℝ | γ.1 p.1 = δ.1 p.2}
  have hS : IsCompact S :=
    (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_eq (γ.2.2.continuous.comp continuous_fst) (δ.2.2.continuous.comp continuous_snd))
  have hdisc : IsDiscrete S := by
    rw [isDiscrete_iff_nhdsNE]
    intro p hp
    rw [inf_principal_eq_bot]
    filter_upwards [b3A_crossing_isolated γ.1 δ.1 γ.2.2 δ.2.2 p.1 p.2 hp.2 (h _ _ hp.2)]
      with q hq hqS
    exact hq hqS.2
  refine (hS.finite hdisc).subset fun p hp ↦ ⟨⟨Ico_subset_Icc_self hp.1, Ico_subset_Icc_self hp.2.1⟩,
    hp.2.2⟩

end Crossings

end HodgeLean.Foundations.Program
