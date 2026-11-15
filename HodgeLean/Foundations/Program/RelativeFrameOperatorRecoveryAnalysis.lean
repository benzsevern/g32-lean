import HodgeLean.Foundations.Program.RelativeFrameOperatorLocalTensor

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_extendBdd_tsupport {U : Set ℂ} (φ : b63r_bddHol U) :
    tsupport (rf4_extendBdd φ) ⊆ closure U := by
  apply closure_mono
  intro z hz
  by_contra hU
  exact hz (by simp only [rf4_extendBdd, dif_neg hU])

theorem rf4_cutoff_coeff_compact {U : Set ℂ} (φ : b63r_bddHol U) (χ : ℂ → ℂ)
    (a : ℂ) (hK : IsCompact (closure U)) :
    HasCompactSupport (fun z ↦ (χ z - a) * rf4_extendBdd φ z) ∧
      tsupport (fun z ↦ (χ z - a) * rf4_extendBdd φ z) ⊆ closure U := by
  have hs : tsupport (fun z ↦ (χ z - a) * rf4_extendBdd φ z) ⊆ closure U :=
    tsupport_mul_subset_right.trans (rf4_extendBdd_tsupport φ)
  exact ⟨hK.of_isClosed_subset (isClosed_tsupport _) hs, hs⟩

theorem rf4_cutoff_coeff_bdd {U : Set ℂ} (φ : b63r_bddHol U) (χ : ℂ → ℂ)
    (a : ℂ) (hK : IsCompact (closure U)) (hχ : ContinuousOn χ (closure U)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖(χ z - a) * rf4_extendBdd φ z‖ ≤ B := by
  classical
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hχ
  have hnonneg : 0 ≤ (max C 0 + ‖a‖) * ‖φ‖ := by positivity
  refine ⟨(max C 0 + ‖a‖) * ‖φ‖, hnonneg, ?_⟩
  intro z
  by_cases hz : z ∈ U
  · have hCh : ‖χ z‖ ≤ max C 0 :=
      (hC z (subset_closure hz)).trans (le_max_left _ _)
    have hleft : ‖χ z - a‖ ≤ max C 0 + ‖a‖ := by
      have hh := norm_sub_le (χ z) a
      linarith
    have hright : ‖rf4_extendBdd φ z‖ ≤ ‖φ‖ := by
      unfold rf4_extendBdd
      rw [dif_pos hz]
      exact φ.val.norm_coe_le_norm ⟨z, hz⟩
    rw [norm_mul]
    exact mul_le_mul hleft hright (norm_nonneg _) (by positivity)
  · simp only [rf4_extendBdd, dif_neg hz, mul_zero, norm_zero]
    exact hnonneg

theorem rf4_outer_cutoff_dbar (n : ℕ) (r : ℝ) (hr : 0 < r) (χ : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ u : ℂ, 7 * r / 4 ≤ ‖u‖ ^ n → χ u = 0)
    (φ : b63r_bddHol (b63r_annulus n r)) (z : ℂ) (hz : ‖z‖ ^ n ≠ r) :
    wirtingerDbar (fun u ↦ χ u * rf4_extendBdd φ u) z =
      rf4_extendBdd φ z * wirtingerDbar χ z := by
  have hA := rf4_annulus_isOpen n r
  have hφ : DifferentiableOn ℂ (rf4_extendBdd φ) (b63r_annulus n r) :=
    (b63r_mem_bddHol_iff hA _).mp φ.property
  have hc : Continuous (fun u : ℂ ↦ ‖u‖ ^ n) := continuous_norm.pow n
  by_cases hl : r < ‖z‖ ^ n
  · by_cases hh : ‖z‖ ^ n < 2 * r
    · have hφz := (hφ.analyticOnNhd hA z ⟨hl, hh⟩).differentiableAt
      rw [rf2_wirtingerDbar_mul (hχ.contDiffAt.differentiableAt (by simp))
        (hφz.restrictScalars ℝ), rf2_wirtingerDbar_hol hφz, mul_zero, zero_add]
    · have hzA : z ∉ b63r_annulus n r := fun h ↦ hh h.2
      have hzeroφ : rf4_extendBdd φ z = 0 := by simp only [rf4_extendBdd, dif_neg hzA]
      rw [hzeroφ, zero_mul]
      apply rf4_wirtingerDbar_eq_zero_of_eventually_constant _ 0 z
      have hlarge : 7 * r / 4 < ‖z‖ ^ n := by linarith
      filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hlarge] with u hu
      rw [hzero u hu.le, zero_mul]
  · have hzA : z ∉ b63r_annulus n r := fun h ↦ hl h.1
    have hzeroφ : rf4_extendBdd φ z = 0 := by simp only [rf4_extendBdd, dif_neg hzA]
    rw [hzeroφ, zero_mul]
    apply rf4_wirtingerDbar_eq_zero_of_eventually_constant _ 0 z
    have hsmall : ‖z‖ ^ n < r := lt_of_le_of_ne (le_of_not_gt hl) hz
    filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hsmall] with u hu
    have huA : u ∉ b63r_annulus n r := fun h ↦ (not_lt_of_ge hu.le) h.1
    simp only [rf4_extendBdd, dif_neg huA, mul_zero]

theorem rf4_inner_cutoff_dbar (n : ℕ) (r : ℝ) (hr : 0 < r) (χ : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hone : ∀ u : ℂ, ‖u‖ ^ n < 5 * r / 4 → χ u = 1)
    (φ : b63r_bddHol (b63r_annulus n r)) (z : ℂ) (hz : ‖z‖ ^ n ≠ 2 * r) :
    wirtingerDbar (fun u ↦ (χ u - 1) * rf4_extendBdd φ u) z =
      rf4_extendBdd φ z * wirtingerDbar χ z := by
  have hA := rf4_annulus_isOpen n r
  have hφ : DifferentiableOn ℂ (rf4_extendBdd φ) (b63r_annulus n r) :=
    (b63r_mem_bddHol_iff hA _).mp φ.property
  have hc : Continuous (fun u : ℂ ↦ ‖u‖ ^ n) := continuous_norm.pow n
  by_cases hl : r < ‖z‖ ^ n
  · by_cases hh : ‖z‖ ^ n < 2 * r
    · have hφz := (hφ.analyticOnNhd hA z ⟨hl, hh⟩).differentiableAt
      have hχz : DifferentiableAt ℝ χ z := hχ.contDiffAt.differentiableAt (by simp)
      have hsub : wirtingerDbar (fun u ↦ χ u - 1) z = wirtingerDbar χ z := by
        unfold wirtingerDbar
        rw [fderiv_sub_const]
      rw [rf2_wirtingerDbar_mul (hχz.sub_const 1) (hφz.restrictScalars ℝ),
        rf2_wirtingerDbar_hol hφz, mul_zero, zero_add, hsub]
    · have hzA : z ∉ b63r_annulus n r := fun h ↦ hh h.2
      have hzeroφ : rf4_extendBdd φ z = 0 := by simp only [rf4_extendBdd, dif_neg hzA]
      rw [hzeroφ, zero_mul]
      apply rf4_wirtingerDbar_eq_zero_of_eventually_constant _ 0 z
      have hbig : 2 * r < ‖z‖ ^ n := lt_of_le_of_ne (le_of_not_gt hh) hz.symm
      filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hbig] with u hu
      have huA : u ∉ b63r_annulus n r := fun h ↦ (not_lt_of_ge hu.le) h.2
      simp only [rf4_extendBdd, dif_neg huA, mul_zero]
  · have hzA : z ∉ b63r_annulus n r := fun h ↦ hl h.1
    have hzeroφ : rf4_extendBdd φ z = 0 := by simp only [rf4_extendBdd, dif_neg hzA]
    rw [hzeroφ, zero_mul]
    apply rf4_wirtingerDbar_eq_zero_of_eventually_constant _ 0 z
    have hsmall : ‖z‖ ^ n < 5 * r / 4 := by linarith
    filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hsmall] with u hu
    rw [hone u hu, sub_self, zero_mul]

theorem rf4_wirtingerDbar_sum {I : Type} (s : Finset I) (f : I → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    wirtingerDbar (fun u ↦ ∑ i ∈ s, f i u) z = ∑ i ∈ s, wirtingerDbar (f i) z := by
  unfold wirtingerDbar
  rw [fderiv_fun_sum hf, map_sum]
  simp only [ContinuousLinearMap.sum_apply]

end HodgeLean.Foundations.Program
