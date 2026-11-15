import HodgeLean.Foundations.Program.SchlesingerPathODE
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

def b65p_laxGenerator (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v t : ι → ℂ) (A : ι → E →L[ℂ] E) (p : ι) : E →L[ℂ] E :=
  ∑ q, if q = p then 0 else ((v p - v q) / (t p - t q)) • A q

theorem b65p_schlesingerField_lax (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v t : ι → ℂ) (A : ι → E →L[ℂ] E) (p : ι) :
    b65p_schlesingerField E v t A p =
      b65p_laxGenerator E v t A p * A p - A p * b65p_laxGenerator E v t A p := by
  unfold b65p_schlesingerField b65p_laxGenerator
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q = p
  · simp [hq]
  · simp [hq, smul_sub, smul_mul_assoc, mul_smul_comm]

theorem b65p_lax_gauge_hasDerivAt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A G H : ℂ → E →L[ℂ] E) (S : E →L[ℂ] E) (z : ℂ)
    (hA : HasDerivAt A (S * A z - A z * S) z)
    (hG : HasDerivAt G (S * G z) z)
    (hH : HasDerivAt H (-H z * S) z) :
    HasDerivAt (fun w ↦ H w * A w * G w) 0 z := by
  convert (hH.mul hA).mul hG using 1
  simp only [Pi.mul_apply]
  noncomm_ring

theorem b65p_lax_conjugacy (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (r : ℝ) (hr : 0 < r)
    (S A : ℂ → E →L[ℂ] E) (hS : AnalyticOnNhd ℂ S (ball 0 r))
    (hA : ∀ z ∈ ball (0 : ℂ) r,
      HasDerivAt A (S z * A z - A z * S z) z) :
    ∀ z ∈ ball (0 : ℂ) r, ∃ G : (E →L[ℂ] E)ˣ,
      A z = G.val * A 0 * (G⁻¹).val := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨Y, hY, hY0, hdY, hbij⟩ := b65_linear_system E S 0 r hr hS
  have hY0' : Y 0 = 1 := hY0
  have hdY' (z : ℂ) (hz : z ∈ ball (0 : ℂ) r) :
      HasDerivAt Y (S z * Y z) z := hdY z hz
  let F : ℂ × (E →L[ℂ] E) → E →L[ℂ] E := fun w ↦ S w.1 * w.2
  have hF : AnalyticAt ℂ F (0, A 0) :=
    ((hS 0 (mem_ball_self hr)).comp (x := (0, A 0)) analyticAt_fst).mul analyticAt_snd
  have hleft (z : ℂ) (hz : z ∈ ball (0 : ℂ) r) :
      HasDerivAt (fun z ↦ A z * Y z) (F (z, A z * Y z)) z := by
    convert (hA z hz).mul (hdY' z hz) using 1
    dsimp [F]
    noncomm_ring
  have hright (z : ℂ) (hz : z ∈ ball (0 : ℂ) r) :
      HasDerivAt (fun z ↦ Y z * A 0) (F (z, Y z * A 0)) z := by
    convert (hdY' z hz).mul_const (A 0) using 1
    dsimp [F]
    noncomm_ring
  have heq := b65p_ode_unique (E →L[ℂ] E) F (A 0) hF r hr
    (fun z ↦ A z * Y z) (fun z ↦ Y z * A 0)
    (by simp [hY0']) (by simp [hY0']) hleft hright
  intro z hz
  obtain ⟨G, hG⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mpr (hbij z hz))
  refine ⟨G, ?_⟩
  have hh := congrArg (fun B : E →L[ℂ] E ↦ B * (G⁻¹).val) (heq hz)
  simpa only [← hG, mul_assoc, Units.val_inv_eq_inv_val, Units.mul_inv, mul_one] using hh

theorem b65p_schlesinger_residue_conjugacy (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (t : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun θ ↦ t θ q) (ball 0 r))
    (hinj : ∀ θ ∈ ball (0 : ℂ) r, Function.Injective (t θ))
    (hA : ∀ θ ∈ ball (0 : ℂ) r, ∀ p, HasDerivAt (fun θ ↦ A θ p)
      (b65p_schlesingerField E (fun q ↦ deriv (fun θ ↦ t θ q) θ) (t θ) (A θ) p) θ) :
    ∀ θ ∈ ball (0 : ℂ) r, ∀ q, ∃ G : (E →L[ℂ] E)ˣ,
      A θ q = G.val * A 0 q * (G⁻¹).val := by
  have hAa (q : ι) : AnalyticOnNhd ℂ (fun z ↦ A z q) (ball (0 : ℂ) r) :=
    (show DifferentiableOn ℂ (fun z ↦ A z q) (ball (0 : ℂ) r) from
      fun z hz ↦ (hA z hz q).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  intro θ hθ p
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hθ
  let S : ℂ → E →L[ℂ] E := fun z ↦
    b65p_laxGenerator E (fun q ↦ deriv (fun z ↦ t z q) z) (t z) (A z) p
  have hS : AnalyticOnNhd ℂ S (ball 0 r) := by
    intro z hz
    unfold S b65p_laxGenerator
    apply Finset.analyticAt_fun_sum
    intro q _
    by_cases hq : q = p
    · simp only [hq, ite_true]
      exact analyticAt_const
    · simp only [ite_eq_right hq]
      exact (((ht p z hz).deriv.sub (ht q z hz).deriv).div
        ((ht p z hz).sub (ht q z hz))
        (sub_ne_zero.mpr (fun h ↦ hq ((hinj z hz) h).symm))).smul (hAa q z hz)
  apply b65p_lax_conjugacy E r hr S (fun z ↦ A z p) hS _ θ hθ
  intro z hz
  simpa only [b65p_schlesingerField_lax] using hA z hz p

def b65p_verticalCoefficient (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (t v : ι → ℂ) (A : ι → E →L[ℂ] E) (x : ℂ) :
    E →L[ℂ] E := -∑ q, (v q / (x - t q)) • A q

theorem b65p_verticalCoefficient_analytic (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
    (r : ℝ) (t : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E) (x : ℂ)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun z ↦ t z q) (ball 0 r))
    (hA : ∀ q, AnalyticOnNhd ℂ (fun z ↦ A z q) (ball 0 r))
    (hx : ∀ z ∈ ball (0 : ℂ) r, ∀ q, x ≠ t z q) :
    AnalyticOnNhd ℂ (fun z ↦ b65p_verticalCoefficient E (t z)
      (fun q ↦ deriv (fun z ↦ t z q) z) (A z) x) (ball 0 r) := by
  intro z hz
  unfold b65p_verticalCoefficient
  apply AnalyticAt.neg
  apply Finset.analyticAt_fun_sum
  intro q _
  exact ((ht q z hz).deriv.div (analyticAt_const.sub (ht q z hz))
    (sub_ne_zero.mpr (hx z hz q))).smul (hA q z hz)

theorem b65p_vertical_gauge (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι]
    (r : ℝ) (hr : 0 < r) (t : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E) (x : ℂ)
    (ht : ∀ q, AnalyticOnNhd ℂ (fun z ↦ t z q) (ball 0 r))
    (hA : ∀ q, AnalyticOnNhd ℂ (fun z ↦ A z q) (ball 0 r))
    (hx : ∀ z ∈ ball (0 : ℂ) r, ∀ q, x ≠ t z q) :
    ∃ Y : ℂ → E →L[ℂ] E, AnalyticOnNhd ℂ Y (ball 0 r) ∧ Y 0 = 1 ∧
      (∀ z ∈ ball (0 : ℂ) r, HasDerivAt Y
        (b65p_verticalCoefficient E (t z) (fun q ↦ deriv (fun z ↦ t z q) z) (A z) x * Y z) z) ∧
      ∀ z ∈ ball (0 : ℂ) r, IsUnit (Y z) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨Y, ha, h0, hd, hb⟩ := b65_linear_system E
    (fun z ↦ b65p_verticalCoefficient E (t z) (fun q ↦ deriv (fun z ↦ t z q) z) (A z) x)
    0 r hr (b65p_verticalCoefficient_analytic E r t A x ht hA hx)
  exact ⟨Y, ha, h0, hd, fun z hz ↦ ContinuousLinearMap.isUnit_iff_bijective.mpr (hb z hz)⟩

end HodgeLean.Foundations.Program
