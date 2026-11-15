import HodgeLean.Foundations.Program.FuchsianSystemNearby

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65f_real_linear_unique {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : ℝ → F →L[ℂ] F) (v : ℝ → ℂ) (f g : ℝ → F) (s t K : ℝ)
    (hf : ∀ q ∈ Icc s t, HasDerivAt f (v q • L q (f q)) q)
    (hg : ∀ q ∈ Icc s t, HasDerivAt g (v q • L q (g q)) q)
    (hb : ∀ q ∈ Icc s t, ‖v q‖ * ‖L q‖ ≤ K) (hfg : f s = g s) :
    ∀ q ∈ Icc s t, f q = g q := by
  let h := fun q ↦ f q - g q
  let h' := fun q ↦ v q • L q (h q)
  have hd : ∀ q ∈ Icc s t, HasDerivAt h (h' q) q := by
    intro q hq
    convert (hf q hq).sub (hg q hq) using 1
    simp only [h, h', map_sub, smul_sub]
  have hh : ContinuousOn h (Icc s t) := fun q hq ↦ (hd q hq).continuousAt.continuousWithinAt
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hh
    (fun q hq ↦ (hd q ⟨hq.1, hq.2.le⟩).hasDerivWithinAt)
    (show h s = 0 by exact sub_eq_zero.mpr hfg) (K := K) (by
      intro q hq
      calc
        ‖h' q‖ = ‖v q‖ * ‖L q (h q)‖ := norm_smul _ _
        _ ≤ ‖v q‖ * (‖L q‖ * ‖h q‖) := mul_le_mul_of_nonneg_left ((L q).le_opNorm _) (norm_nonneg _)
        _ = (‖v q‖ * ‖L q‖) * ‖h q‖ := by ring
        _ ≤ K * ‖h q‖ := mul_le_mul_of_nonneg_right (hb q ⟨hq.1, hq.2.le⟩) (norm_nonneg _))
  exact fun q hq ↦ sub_eq_zero.mp (hzero q hq)

theorem b65f_smooth_transport_propagates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {A : ℂ → E →L[ℂ] E} {U : Set ℂ} (hU : IsOpen U) (hA : AnalyticOnNhd ℂ A U)
    (γ v : ℝ → ℂ) (Q : ℝ → E →L[ℂ] E)
    (hγ : ContinuousOn γ (Icc 0 1)) (hv : ContinuousOn v (Icc 0 1))
    (hm : MapsTo γ (Icc 0 1) U)
    (hdγ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (v t) t)
    (hdQ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt Q (v t • (A (γ t) * Q t)) t) :
    b65f_transport E A γ * Q 0 = Q 1 := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨r, hr, hsub⟩ := (isCompact_Icc.image_of_continuousOn hγ).exists_thickening_subset_open
    hU (image_subset_iff.mpr hm)
  obtain ⟨ε, hε, he⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hγ) r hr
  have hcoeff : ContinuousOn (fun t ↦ ‖v t‖ * ‖A (γ t)‖) (Icc (0 : ℝ) 1) :=
    hv.norm.mul (hA.continuousOn.comp hγ hm).norm
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hcoeff
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖v t‖ * ‖A (γ t)‖ ≤ K :=
    (le_abs_self _).trans (hK t ht)
  have hlim : Tendsto (fun N : ℕ ↦ ((2 : ℝ) ^ N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hp : ∀ᶠ N in atTop, b65f_polygon E A γ N * Q 0 = Q 1 := by
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with N hN
    let k := 2 ^ N
    have hk : 0 < k := pow_pos (by norm_num) N
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hkR : (k : ℝ) = (2 : ℝ) ^ N := by simp [k]
    have ht (i : ℕ) (hi : i ≤ k) : (i : ℝ) / k ∈ Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · exact (div_le_one (by positivity : (0 : ℝ) < k)).mpr (by exact_mod_cast hi)
    have hs (i : ℕ) (hi : i < k) :
        b65f_segment E A (γ ((i : ℝ) / k)) (γ (((i : ℝ) + 1) / k)) * Q ((i : ℝ) / k) =
          Q (((i : ℝ) + 1) / k) := by
      let s : ℝ := (i : ℝ) / k
      let t : ℝ := ((i : ℝ) + 1) / k
      have hs0 := ht i hi.le
      have ht1 : t ∈ Icc (0 : ℝ) 1 := by
        dsimp [t]
        exact_mod_cast ht (i + 1) (by omega)
      have hst : s ≤ t := by dsimp [s, t]; gcongr; linarith
      have hmem (q : ℝ) (hq : q ∈ Icc s t) : q ∈ Icc (0 : ℝ) 1 :=
        ⟨hs0.1.trans hq.1, hq.2.trans ht1.2⟩
      have hγball (q : ℝ) (hq : q ∈ Icc s t) : γ q ∈ ball (γ s) r := by
        apply he _ (hmem q hq) _ hs0
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hq.1)]
        have hlen : t - s = ((2 : ℝ) ^ N)⁻¹ := by dsimp [s, t]; rw [hkR]; field_simp; ring
        have hqt := hq.2
        linarith
      have hball : ball (γ s) r ⊆ U :=
        (ball_subset_thickening (mem_image_of_mem γ hs0) r).trans hsub
      let f := fun q ↦ b65f_segment E A (γ s) (γ q) * Q s
      have hdf : ∀ q ∈ Icc s t, HasDerivAt f (v q • (A (γ q) * f q)) q := by
        intro q hq
        have hh := ((b65f_segment_hasDerivAt (hA.mono hball) (hγball q hq)).scomp q
          (hdγ q (hmem q hq))).mul_const (Q s)
        simpa only [f, smul_mul_assoc, mul_assoc, Function.comp_apply] using hh
      have hsame := b65f_real_linear_unique (fun q ↦ b65f_leftCoefficient A (γ q)) v f Q s t K
        hdf (fun q hq ↦ hdQ q (hmem q hq)) (fun q hq ↦
          (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_mul_apply_le ℂ (E →L[ℂ] E) (A (γ q))) (norm_nonneg _)).trans
              (hb q (hmem q hq))) (by simp [f, b65f_segment_initial])
      exact hsame t ⟨hst, le_rfl⟩
    have hh := b65f_reverse_product_propagates
      (fun i ↦ b65f_segment E A (γ ((i : ℝ) / k)) (γ (((i : ℝ) + 1) / k)))
      (fun i ↦ Q ((i : ℝ) / k)) k (by intro i hi; simpa only [Nat.cast_add, Nat.cast_one] using hs i hi)
    simpa [b65f_polygon, hkR, hk0] using hh
  have ht := (b65f_transport_converges hU hA γ hγ hm).mul_const (Q 0)
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hp))

end HodgeLean.Foundations.Program
