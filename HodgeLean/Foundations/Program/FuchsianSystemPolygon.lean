import HodgeLean.Foundations.Program.FuchsianSystemUnique
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65f_reverse_product_propagates {M : Type*} [Monoid M]
    (T w : ℕ → M) (n : ℕ) (h : ∀ i < n, T i * w i = w (i + 1)) :
    (List.ofFn (fun i : Fin n ↦ T i.val)).reverse.prod * w 0 = w n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ']
    simp only [Fin.val_castSucc, Fin.val_last, List.concat_eq_append, List.reverse_concat, List.prod_cons]
    rw [mul_assoc, ih (fun i hi ↦ h i (by omega)), h n (by omega)]

theorem b65f_polygon_eventually_propagates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    {A Y : ℂ → E →L[ℂ] E} {U : Set ℂ} (hU : IsOpen U)
    (hA : AnalyticOnNhd ℂ A U)
    (hY : ∀ z ∈ U, HasDerivAt Y (A z * Y z) z)
    (γ : ℝ → ℂ) (hc : ContinuousOn γ (Icc 0 1))
    (hm : MapsTo γ (Icc 0 1) U) :
    ∀ᶠ N in atTop, b65f_polygon E A γ N * Y (γ 0) = Y (γ 1) := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_Icc.image_of_continuousOn hc).exists_thickening_subset_open
    hU (image_subset_iff.mpr hm)
  obtain ⟨ε, hε, he⟩ := Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous hc) δ hδ
  have hlim : Tendsto (fun N : ℕ ↦ ((2 : ℝ) ^ N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with N hN
  let n := 2 ^ N
  have hn : 0 < n := pow_pos (by norm_num) N
  have hnR : (n : ℝ) = (2 : ℝ) ^ N := by simp [n]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have ht (i : ℕ) (hi : i ≤ n) : (i : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < n)).mpr
      exact_mod_cast hi
  have hstep (i : ℕ) (hi : i < n) :
      b65f_segment E A (γ ((i : ℝ) / n)) (γ (((i : ℝ) + 1) / n)) *
        Y (γ ((i : ℝ) / n)) = Y (γ (((i : ℝ) + 1) / n)) := by
    have hi0 := ht i hi.le
    have hi1 : ((i : ℝ) + 1) / n ∈ Icc (0 : ℝ) 1 := by
      exact_mod_cast ht (i + 1) (by omega)
    have hdist : dist (((i : ℝ) + 1) / n) ((i : ℝ) / n) < ε := by
      rw [Real.dist_eq, div_sub_div_same, add_sub_cancel_left, abs_of_nonneg (by positivity)]
      simpa [one_div, hnR] using hN
    have hball : ball (γ ((i : ℝ) / n)) δ ⊆ U :=
      (ball_subset_thickening (mem_image_of_mem γ hi0) δ).trans hsub
    apply b65f_segment_propagates hδ (hA.mono hball)
      (fun z hz ↦ hY z (hball hz))
    exact he _ hi1 _ hi0 hdist
  have hh := b65f_reverse_product_propagates
    (fun i ↦ b65f_segment E A (γ ((i : ℝ) / n)) (γ (((i : ℝ) + 1) / n)))
    (fun i ↦ Y (γ ((i : ℝ) / n))) n (by
      intro i hi
      simpa only [Nat.cast_add, Nat.cast_one] using hstep i hi)
  simpa [b65f_polygon, hnR, hn0] using hh

end HodgeLean.Foundations.Program
