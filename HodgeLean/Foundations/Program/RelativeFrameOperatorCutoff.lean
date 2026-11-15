import HodgeLean.Foundations.Program.RelativeFrameOperatorGluing

set_option maxHeartbeats 400000

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program
local instance rf4_decidableCutoff (p : Prop) : Decidable p := Classical.propDecidable p

theorem rf4_annulus_cutoff (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ ∞ χ ∧
      (∀ u : ℂ, ‖u‖ ^ n < 5 * r / 4 → χ u = 1) ∧
      (∀ u : ℂ, 7 * r / 4 ≤ ‖u‖ ^ n → χ u = 0) := by
  obtain ⟨η, hη, _, hsη, hoη⟩ := rf2_cutoff (5 * r / 4) (7 * r / 4)
    (by positivity) (by linarith)
  refine ⟨fun u ↦ η (u ^ n), hη.comp (contDiff_id.pow n), ?_, ?_⟩
  · intro u hu
    apply hoη
    simpa only [Metric.mem_ball, dist_zero_right, norm_pow] using hu
  · intro u hu
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hlt : ‖u‖ ^ n < 7 * r / 4 := by
      simpa only [Metric.mem_ball, dist_zero_right, norm_pow] using hsη h
    linarith

theorem rf4_wirtingerDbar_eq_zero_of_eventually_constant (f : ℂ → ℂ) (c z : ℂ)
    (h : f =ᶠ[𝓝 z] fun _ ↦ c) : wirtingerDbar f z = 0 := by
  unfold wirtingerDbar
  rw [h.fderiv_eq]
  simp

theorem rf4_annulus_cutoff_dbar (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ ∞ χ ∧
      (∀ u : ℂ, ‖u‖ ^ n < 5 * r / 4 → χ u = 1) ∧
      (∀ u : ℂ, 7 * r / 4 ≤ ‖u‖ ^ n → χ u = 0) ∧
      HasCompactSupport (wirtingerDbar χ) ∧
        tsupport (wirtingerDbar χ) ⊆ b63r_annulus n r := by
  obtain ⟨χ, hχ, hone, hzero⟩ := rf4_annulus_cutoff n r hr
  let K : Set ℂ := {u | 5 * r / 4 ≤ ‖u‖ ^ n ∧ ‖u‖ ^ n ≤ 7 * r / 4}
  have hc : Continuous (fun u : ℂ ↦ ‖u‖ ^ n) := continuous_norm.pow n
  have hK : IsClosed K := (isClosed_le continuous_const hc).inter
    (isClosed_le hc continuous_const)
  have hs : Function.support (wirtingerDbar χ) ⊆ K := by
    intro u hu
    have hne : wirtingerDbar χ u ≠ 0 := hu
    constructor
    · by_contra hsmall
      have hl : ‖u‖ ^ n < 5 * r / 4 := lt_of_not_ge hsmall
      have hN : ∀ᶠ v in 𝓝 u, ‖v‖ ^ n < 5 * r / 4 :=
        (isOpen_lt hc continuous_const).mem_nhds hl
      apply hne
      apply rf4_wirtingerDbar_eq_zero_of_eventually_constant χ 1 u
      filter_upwards [hN] with v hv
      exact hone v hv
    · by_contra hbig
      have hl : 7 * r / 4 < ‖u‖ ^ n := lt_of_not_ge hbig
      have hN : ∀ᶠ v in 𝓝 u, 7 * r / 4 < ‖v‖ ^ n :=
        (isOpen_lt continuous_const hc).mem_nhds hl
      apply hne
      apply rf4_wirtingerDbar_eq_zero_of_eventually_constant χ 0 u
      filter_upwards [hN] with v hv
      exact hzero v hv.le
  have hts : tsupport (wirtingerDbar χ) ⊆ K := closure_minimal hs hK
  have hAnn : tsupport (wirtingerDbar χ) ⊆ b63r_annulus n r := by
    intro u hu
    obtain ⟨hl, hh⟩ := hts hu
    change r < ‖u‖ ^ n ∧ ‖u‖ ^ n < 2 * r
    constructor <;> linarith
  have hcompact : HasCompactSupport (wirtingerDbar χ) :=
    (rf4_closedAnnulus_isCompact hn r).of_isClosed_subset (isClosed_tsupport _)
      (hAnn.trans (rf4_annulus_subset_closed n r))
  exact ⟨χ, hχ, hone, hzero, hcompact, hAnn⟩

theorem rf4_supported_mul_extend (U : Set ℂ) (hU : IsOpen U) (f g : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ U) :
    ContDiff ℝ ∞ (fun z ↦ if z ∈ U then f z * g z else 0) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ U
  · apply (((hf z hz).contDiffAt (hU.mem_nhds hz)).mul hg.contDiffAt).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hz] with w hw
    exact ite_eq_left hw
  · have hz' : z ∉ tsupport g := fun h ↦ hz (hs h)
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℂ ↦ (0 : ℂ)) z).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hz'] with w hw
    have hw' := image_eq_zero_of_notMem_tsupport hw
    simp only [hw', mul_zero, ite_self]

theorem rf4_annulus_density_smooth (n : ℕ) (r : ℝ) (χ : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport (wirtingerDbar χ))
    (hs : tsupport (wirtingerDbar χ) ⊆ b63r_annulus n r)
    (φ : b63r_bddHol (b63r_annulus n r)) :
    ContDiff ℝ ∞ (fun z ↦ rf4_extendBdd φ z * wirtingerDbar χ z) ∧
      HasCompactSupport (fun z ↦ rf4_extendBdd φ z * wirtingerDbar χ z) ∧
        tsupport (fun z ↦ rf4_extendBdd φ z * wirtingerDbar χ z) ⊆ b63r_annulus n r := by
  have hU := rf4_annulus_isOpen n r
  have hf : DifferentiableOn ℂ (rf4_extendBdd φ) (b63r_annulus n r) :=
    (b63r_mem_bddHol_iff hU _).mp φ.property
  have hfr : ContDiffOn ℝ ∞ (rf4_extendBdd φ) (b63r_annulus n r) :=
    ((hf.analyticOnNhd hU).contDiffOn hU.uniqueDiffOn).restrict_scalars ℝ
  have hg : ContDiff ℝ ∞ (wirtingerDbar χ) :=
    contDiffOn_univ.mp (rf2_wirtingerDbar_contDiffOn isOpen_univ hχ.contDiffOn)
  have he := rf4_supported_mul_extend (b63r_annulus n r) hU (rf4_extendBdd φ)
    (wirtingerDbar χ) hfr hg hs
  have hEq : (fun z ↦ if z ∈ b63r_annulus n r then rf4_extendBdd φ z * wirtingerDbar χ z else 0) =
      (fun z ↦ rf4_extendBdd φ z * wirtingerDbar χ z) := by
    funext z
    by_cases hz : z ∈ b63r_annulus n r <;> simp [rf4_extendBdd, hz]
  rw [hEq] at he
  have hts : tsupport (fun z ↦ rf4_extendBdd φ z * wirtingerDbar χ z) ⊆
      tsupport (wirtingerDbar χ) := tsupport_mul_subset_right
  exact ⟨he, hc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hs⟩

end HodgeLean.Foundations.Program
