import HodgeLean.Foundations.Program.RelativeFrameOperatorRecoveryGeometry

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_wirtingerDbar_add {g h : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) (hh : DifferentiableAt ℝ h z) :
    wirtingerDbar (fun u ↦ g u + h u) z = wirtingerDbar g z + wirtingerDbar h z := by
  unfold wirtingerDbar
  rw [fderiv_fun_add hg hh, map_add, ContinuousLinearMap.add_apply]

theorem rf4_cutoff_correction_analytic (U : Set ℂ) (hU : IsOpen U)
    (φ χ v : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ U)
    (hχ : ContDiffOn ℝ ∞ χ U) (hv : ContDiffOn ℝ ∞ v U)
    (hd : ∀ z ∈ U, wirtingerDbar v z = -φ z * wirtingerDbar χ z) (a : ℂ) :
    AnalyticOnNhd ℂ (fun z ↦ (χ z - a) * φ z + v z) U := by
  have hφr : ContDiffOn ℝ ∞ φ U :=
    ((hφ.analyticOnNhd hU).contDiffOn hU.uniqueDiffOn).restrict_scalars ℝ
  apply rf2_analyticOnNhd_of_wirtinger_zero U hU _
    (((hχ.sub contDiffOn_const).mul hφr).add hv)
  intro z hz
  have hχz : DifferentiableAt ℝ χ z :=
    ((hχ z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hvz : DifferentiableAt ℝ v z :=
    ((hv z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hφz := (hφ.analyticOnNhd hU z hz).differentiableAt
  have hsub : wirtingerDbar (fun u ↦ χ u - a) z = wirtingerDbar χ z := by
    unfold wirtingerDbar
    rw [fderiv_sub_const]
  have hmul : DifferentiableAt ℝ (fun u ↦ (χ u - a) * φ u) z :=
    (hχz.sub_const a).mul (hφz.restrictScalars ℝ)
  rw [rf4_wirtingerDbar_add hmul hvz,
    rf2_wirtingerDbar_mul (hχz.sub_const a) (hφz.restrictScalars ℝ),
    rf2_wirtingerDbar_hol hφz, hsub, hd z hz]
  ring

theorem rf4_outer_cutoff_smooth (n : ℕ) (r : ℝ) (hr : 0 < r) (χ : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ u : ℂ, 7 * r / 4 ≤ ‖u‖ ^ n → χ u = 0)
    (φ : b63r_bddHol (b63r_annulus n r)) (z : ℂ) (hz : ‖z‖ ^ n ≠ r) :
    ContDiffAt ℝ ∞ (fun u ↦ χ u * rf4_extendBdd φ u) z := by
  have hA := rf4_annulus_isOpen n r
  have hφ : DifferentiableOn ℂ (rf4_extendBdd φ) (b63r_annulus n r) :=
    (b63r_mem_bddHol_iff hA _).mp φ.property
  have hφr : ContDiffOn ℝ ∞ (rf4_extendBdd φ) (b63r_annulus n r) :=
    ((hφ.analyticOnNhd hA).contDiffOn hA.uniqueDiffOn).restrict_scalars ℝ
  have hc : Continuous (fun u : ℂ ↦ ‖u‖ ^ n) := continuous_norm.pow n
  by_cases hl : r < ‖z‖ ^ n
  · by_cases hh : ‖z‖ ^ n < 2 * r
    · exact hχ.contDiffAt.mul ((hφr z ⟨hl, hh⟩).contDiffAt (hA.mem_nhds ⟨hl, hh⟩))
    · have hlarge : 7 * r / 4 < ‖z‖ ^ n := by linarith
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℂ ↦ (0 : ℂ)) z).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hlarge] with u hu
      rw [hzero u hu.le, zero_mul]
  · have hsmall : ‖z‖ ^ n < r := lt_of_le_of_ne (le_of_not_gt hl) hz
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℂ ↦ (0 : ℂ)) z).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hsmall] with u hu
    have huA : u ∉ b63r_annulus n r := fun h ↦ (not_lt_of_ge hu.le) h.1
    simp only [rf4_extendBdd, dif_neg huA, mul_zero]

theorem rf4_inner_cutoff_smooth (n : ℕ) (r : ℝ) (hr : 0 < r) (χ : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hone : ∀ u : ℂ, ‖u‖ ^ n < 5 * r / 4 → χ u = 1)
    (φ : b63r_bddHol (b63r_annulus n r)) (z : ℂ) (hz : ‖z‖ ^ n ≠ 2 * r) :
    ContDiffAt ℝ ∞ (fun u ↦ (χ u - 1) * rf4_extendBdd φ u) z := by
  have hA := rf4_annulus_isOpen n r
  have hφ : DifferentiableOn ℂ (rf4_extendBdd φ) (b63r_annulus n r) :=
    (b63r_mem_bddHol_iff hA _).mp φ.property
  have hφr : ContDiffOn ℝ ∞ (rf4_extendBdd φ) (b63r_annulus n r) :=
    ((hφ.analyticOnNhd hA).contDiffOn hA.uniqueDiffOn).restrict_scalars ℝ
  have hc : Continuous (fun u : ℂ ↦ ‖u‖ ^ n) := continuous_norm.pow n
  by_cases hl : r < ‖z‖ ^ n
  · by_cases hh : ‖z‖ ^ n < 2 * r
    · exact (hχ.contDiffAt.sub contDiffAt_const).mul
        ((hφr z ⟨hl, hh⟩).contDiffAt (hA.mem_nhds ⟨hl, hh⟩))
    · have hbig : 2 * r < ‖z‖ ^ n := lt_of_le_of_ne (le_of_not_gt hh) hz.symm
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℂ ↦ (0 : ℂ)) z).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hbig] with u hu
      have huA : u ∉ b63r_annulus n r := fun h ↦ (not_lt_of_ge hu.le) h.2
      simp only [rf4_extendBdd, dif_neg huA, mul_zero]
  · have hsmall : ‖z‖ ^ n < 5 * r / 4 := by linarith
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℂ ↦ (0 : ℂ)) z).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hsmall] with u hu
    rw [hone u hu, sub_self, zero_mul]

end HodgeLean.Foundations.Program
