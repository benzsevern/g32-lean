import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C]
attribute [local instance] b3Forms_isManifold_real

theorem radial_chart_derivative_density (hE : Module.finrank ℂ E = 1)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : HurwitzPrymRR_IsLinear θ)
    (hs : ∀ q, ContDiffAt ℝ ∞ (HurwitzPrymRR_loc hE θ q) 0)
    (x : C) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hball : ∀ z : ℂ, ‖z‖ ≤ b →
      chartAt E x x + b4cov_lineEquiv hE z ∈ (chartAt E x).target)
    (G : ℂ → ℂ) (hG : ∀ z : ℂ, ‖z‖ < b → z ≠ 0 → AnalyticAt ℂ G z)
    (hcoef : ∀ z : ℂ, chartAt E x x + b4cov_lineEquiv hE z ∈ (chartAt E x).target →
      b4c_residue_chartFunction hE x (fun t => b4c_residue_profile a b ‖t‖)
        ((chartAt E x).symm (chartAt E x x + b4cov_lineEquiv hE z)) ≠ 0 →
      HurwitzPrymRR_loc hE θ x =ᶠ[𝓝 z]
        fun u => (1 - (b4c_residue_profile (a / 2) a ‖u‖ : ℂ)) * G u)
    (P : ℂ →L[ℝ] ℝ) (z : ℂ) :
    b3Forms_chartFun (b4c_residue_basis hE) x
      (b3Forms_smulFun (b4c_residue_chartFunction hE x
        (fun t => b4c_residue_profile a b ‖t‖))
        (b3Forms_d (b4c_residue_realForm hE θ P)))
      (chartAt E x x + b4cov_lineEquiv hE z) =
      P (-(((deriv (b4c_residue_profile (a / 2) a) ‖z‖ : ℝ) : ℂ) *
        (z * Complex.I / ‖z‖) * G z)) := by
  have ha2 : 0 < a / 2 := by positivity
  have haa : a / 2 < a := by linarith
  let χ := b4c_residue_chartFunction hE x (fun t ↦ b4c_residue_profile a b ‖t‖)
  let A : ℂ → E := fun t ↦ chartAt E x x + b4cov_lineEquiv hE t
  let y := (chartAt E x).symm (A z)
  have hzero : a < ‖z‖ → deriv (b4c_residue_profile (a / 2) a) ‖z‖ = 0 := by
    intro hza
    exact b4c_residue_profile_deriv haa (fun h ↦ (not_le.mpr hza) h.2)
  by_cases ht : A z ∈ (chartAt E x).target
  · rw [b3Forms_chartFun, Set.indicator_of_mem ht, b3Forms_loc_smulFun]
    change χ y * b3Forms_loc (b3Forms_d (b4c_residue_realForm hE θ P)) x (A z)
      (b4c_residue_basis hE) = _
    have hχcoord : χ y = b4c_residue_profile a b ‖z‖ :=
      b4c_residue_chartFunction_coordinates hE x _ ht
    by_cases hχ : χ y = 0
    · have hza : a < ‖z‖ := by
        by_contra hn
        have hh := b4c_residue_profile_one hab (le_of_not_gt hn)
        rw [hh] at hχcoord
        exact zero_ne_one (hχ.symm.trans hχcoord)
      simp [hχ, hzero hza]
    · have hzb : ‖z‖ < b := by
        by_contra hn
        exact hχ (hχcoord.trans (b4c_residue_profile_zero hab (le_of_not_gt hn)))
      have he := hcoef z ht hχ
      have hrad := b4c_residue_radial_product (G := G) ha2 haa (hG z hzb)
      have hdiff : DifferentiableAt ℝ (HurwitzPrymRR_loc hE θ x) z :=
        hrad.1.congr_of_eventuallyEq he
      rw [b4c_residue_basis_coe, b4c_residue_loc_derivative hE θ hθ P
        hs x z ht hdiff,
        he.fderiv_eq, hrad.2]
      by_cases hza : ‖z‖ ≤ a
      · rw [hχcoord, b4c_residue_profile_one hab hza, one_mul]
      · simp [hzero (lt_of_not_ge hza)]
  · have hzb : b < ‖z‖ := by
      by_contra hn
      exact ht (hball z (le_of_not_gt hn))
    rw [b3Forms_chartFun, Set.indicator_of_notMem ht]
    simp [hzero (hab.trans hzb)]

variable [MeasurableSpace E] [BorelSpace E]

theorem radial_chart_integral_of_local_density (hE : Module.finrank ℂ E = 1)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : HurwitzPrymRR_IsLinear θ)
    (hs : ∀ q, ContDiffAt ℝ ∞ (HurwitzPrymRR_loc hE θ q) 0)
    (x : C) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hball : ∀ z : ℂ, ‖z‖ ≤ b →
      chartAt E x x + b4cov_lineEquiv hE z ∈ (chartAt E x).target)
    (G : ℂ → ℂ) (hG : ∀ z : ℂ, ‖z‖ < b → z ≠ 0 → AnalyticAt ℂ G z)
    (hcoef : ∀ z : ℂ, chartAt E x x + b4cov_lineEquiv hE z ∈ (chartAt E x).target →
      b4c_residue_chartFunction hE x (fun t => b4c_residue_profile a b ‖t‖)
        ((chartAt E x).symm (chartAt E x x + b4cov_lineEquiv hE z)) ≠ 0 →
      HurwitzPrymRR_loc hE θ x =ᶠ[𝓝 z]
        fun u => (1 - (b4c_residue_profile (a / 2) a ‖u‖ : ℂ)) * G u)
    (r : ℂ)
    (hlocal : (∫ z : ℂ, (((deriv (b4c_residue_profile (a / 2) a) ‖z‖ : ℝ) : ℂ) *
      (z * Complex.I / ‖z‖) * G z)) = -(2 * (Real.pi : ℂ) * Complex.I * r))
    (P : ℂ →L[ℝ] ℝ) :
    b3Forms_chartIntegral (b4c_residue_basis hE) x
      (b3Forms_smulFun (b4c_residue_chartFunction hE x
        (fun t => b4c_residue_profile a b ‖t‖))
        (b3Forms_d (b4c_residue_realForm hE θ P))) =
      P (2 * (Real.pi : ℂ) * Complex.I * r) := by
  have ha2 : 0 < a / 2 := by positivity
  have haa : a / 2 < a := by linarith
  have hInt := b4c_residue_density_integrable ha2 haa (fun z hz =>
    hG z (hz.2.trans_lt hab) (norm_pos_iff.mp (ha2.trans_le hz.1)))
  have hIntNeg : Integrable (fun z : ℂ =>
      -(((deriv (b4c_residue_profile (a / 2) a) ‖z‖ : ℝ) : ℂ) *
        (z * Complex.I / ‖z‖) * G z)) := hInt.fun_neg
  rw [b4c_residue_chartIntegral_coordinates]
  simp_rw [radial_chart_derivative_density hE θ hθ hs x ha hab hball G hG hcoef P]
  rw [P.integral_comp_comm hIntNeg, integral_neg, hlocal, neg_neg]

end HodgeLean.Foundations.Curves.AbelTheorem
