import HodgeLean.Foundations.Program.FuchsianSystemRefinement

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65f_reverseProduct_isUnit {M : Type*} [Monoid M] (f : ℕ → M) (n : ℕ)
    (h : ∀ i < n, IsUnit (f i)) : IsUnit (b65f_reverseProduct f n) := by
  induction n with
  | zero => simp [b65f_reverseProduct]
  | succ n ih =>
    rw [b65f_reverseProduct_succ]
    exact (h n (by omega)).mul (ih (fun i hi ↦ h i (by omega)))

theorem b65f_polygon_stabilizes {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {A : ℂ → E →L[ℂ] E} {U : Set ℂ} (hU : IsOpen U)
    (hA : AnalyticOnNhd ℂ A U) (γ : ℝ → ℂ)
    (hc : ContinuousOn γ (Icc 0 1)) (hm : MapsTo γ (Icc 0 1) U) :
    ∃ N : ℕ, IsUnit (b65f_polygon E A γ N) ∧
      ∀ M ≥ N, b65f_polygon E A γ M = b65f_polygon E A γ N := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_Icc.image_of_continuousOn hc).exists_thickening_subset_open
    hU (image_subset_iff.mpr hm)
  obtain ⟨ε, hε, he⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) (δ / 4) (by positivity)
  have hlim : Tendsto (fun N : ℕ ↦ ((2 : ℝ) ^ N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  have hlocal (n : ℕ) (hn : N ≤ n) :
      IsUnit (b65f_polygon E A γ n) ∧
      b65f_polygon E A γ (n + 1) = b65f_polygon E A γ n := by
    let k := 2 ^ n
    have hk : 0 < k := pow_pos (by norm_num) n
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hkR : (k : ℝ) = (2 : ℝ) ^ n := by simp [k]
    have hsmall : (k : ℝ)⁻¹ < ε := by simpa [hkR] using hN n hn
    have ht (i : ℕ) (hi : i ≤ k) : (i : ℝ) / k ∈ Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · exact (div_le_one (by positivity : (0 : ℝ) < k)).mpr (by exact_mod_cast hi)
    let f : ℕ → E →L[ℂ] E := fun i ↦
      b65f_segment E A (γ ((i : ℝ) / k)) (γ (((i : ℝ) + 1) / k))
    let g : ℕ → E →L[ℂ] E := fun i ↦
      b65f_segment E A (γ ((i : ℝ) / (2 * k))) (γ (((i : ℝ) + 1) / (2 * k)))
    have hpoints (i : ℕ) (hi : i < k) :
        dist (γ (((i : ℝ) + 1) / k)) (γ ((i : ℝ) / k)) < δ / 4 ∧
        dist (γ ((2 * (i : ℝ) + 1) / (2 * k))) (γ ((i : ℝ) / k)) < δ / 4 := by
      have hi0 := ht i hi.le
      have hi1 : ((i : ℝ) + 1) / k ∈ Icc (0 : ℝ) 1 := by
        exact_mod_cast ht (i + 1) (by omega)
      have him : (2 * (i : ℝ) + 1) / (2 * k) ∈ Icc (0 : ℝ) 1 := by
        constructor
        · positivity
        · apply (div_le_one (by positivity : (0 : ℝ) < 2 * k)).mpr
          have hile : (i : ℝ) + 1 ≤ k := by exact_mod_cast (show i + 1 ≤ k by omega)
          linarith
      have hd1 : dist (((i : ℝ) + 1) / k) ((i : ℝ) / k) < ε := by
        rw [Real.dist_eq, div_sub_div_same, add_sub_cancel_left, abs_of_nonneg (by positivity)]
        simpa only [one_div] using hsmall
      have hdm : dist ((2 * (i : ℝ) + 1) / (2 * k)) ((i : ℝ) / k) < ε := by
        rw [Real.dist_eq, show (2 * (i : ℝ) + 1) / (2 * k) - (i : ℝ) / k =
          1 / (2 * k) by field_simp; ring, abs_of_nonneg (by positivity)]
        have hh : 1 / (2 * (k : ℝ)) ≤ (k : ℝ)⁻¹ := by
          rw [← one_div]
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith [show (0 : ℝ) ≤ k by positivity]
        exact hh.trans_lt hsmall
      exact ⟨he _ hi1 _ hi0 hd1, he _ him _ hi0 hdm⟩
    have hball (i : ℕ) (hi : i < k) : ball (γ ((i : ℝ) / k)) δ ⊆ U :=
      (ball_subset_thickening (mem_image_of_mem γ (ht i hi.le)) δ).trans hsub
    have hu : IsUnit (b65f_reverseProduct f k) := by
      apply b65f_reverseProduct_isUnit
      intro i hi
      apply b65f_regular_solution_isUnit hδ (hA.mono (hball i hi))
        (fun z hz ↦ b65f_segment_hasDerivAt (hA.mono (hball i hi)) hz)
        (b65f_segment_initial E A _)
      exact mem_ball.mpr (by have hh := (hpoints i hi).1; linarith)
    have hpairs : ∀ i < k, g (2 * i + 1) * g (2 * i) = f i := by
      intro i hi
      have hh := b65f_segment_local_cocycle hδ (hA.mono (hball i hi))
        (hpoints i hi).2 (hpoints i hi).1
      have ht0 : (2 * (i : ℝ)) / (2 * k) = (i : ℝ) / k := by field_simp
      have ht1 : (2 * (i : ℝ) + 1 + 1) / (2 * k) = ((i : ℝ) + 1) / k := by field_simp; ring
      simpa [f, g, Nat.cast_add, Nat.cast_mul, ht0, ht1] using hh
    have hp : b65f_reverseProduct g (2 * k) = b65f_reverseProduct f k :=
      (b65f_reverseProduct_pairs g k).trans (b65f_reverseProduct_congr hpairs)
    constructor
    · simpa [b65f_polygon, b65f_reverseProduct, f, hkR] using hu
    · simpa [b65f_polygon, b65f_reverseProduct, f, g, k, pow_succ, mul_comm] using hp
  refine ⟨N, (hlocal N le_rfl).1, ?_⟩
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => rfl
  | succ M hM ih => exact (hlocal M hM).2.trans ih

end HodgeLean.Foundations.Program
