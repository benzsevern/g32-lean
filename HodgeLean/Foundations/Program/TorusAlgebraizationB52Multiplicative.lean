import HodgeLean.Foundations.Program.TorusAlgebraizationB52Functional
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b52_three_product_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ℂ) {U : Set E} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hgne : ∀ x ∈ U, g x ≠ 0) (k : E) (C : ℂ)
    (hprod : ∀ x ∈ U, ∀ y ∈ U, k - x - y ∈ U → g x * g y * g (k - x - y) = C)
    (b t : E) (hb : b ∈ U) (ht : t ∈ U) (hbt : k - t - b ∈ U) :
    fderiv ℂ g t = g t • ((g b)⁻¹ • fderiv ℂ g b) := by
  let x := k - t - b
  have hxt : k - x - b = t := by dsimp [x]; abel
  have hn : {y : E | y ∈ U ∧ k - x - y ∈ U} ∈ 𝓝 b :=
    (hU.inter (hU.preimage (continuous_const.sub continuous_id))).mem_nhds
      ⟨hb, by change k - x - b ∈ U; rwa [hxt]⟩
  have he : (fun y ↦ g x * g y * g (k - x - y)) =ᶠ[𝓝 b] (fun _ ↦ C) := by
    filter_upwards [hn] with y hy
    exact hprod x hbt y hy.1 hy.2
  have hb' := hg.differentiableAt (hU.mem_nhds hb)
  have ht' := hg.differentiableAt (hU.mem_nhds (show k - x - b ∈ U by rwa [hxt]))
  have hd := (hb'.hasFDerivAt.const_mul (g x)).mul
    (ht'.hasFDerivAt.comp b ((hasFDerivAt_const (k - x) b).sub (hasFDerivAt_id b)))
  simp only [Function.comp_def, id_eq, Pi.mul_def] at hd
  have hz := hd.unique ((hasFDerivAt_const C b).congr_of_eventuallyEq he)
  ext v
  have hv := congrArg (fun A : E →L[ℂ] ℂ ↦ A v) hz
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply, zero_sub,
    smul_eq_mul, map_neg, hxt] at hv
  have hm : g x * (g t * fderiv ℂ g b v - g b * fderiv ℂ g t v) = 0 := by
    linear_combination hv
  have hh := (mul_eq_zero.mp hm).resolve_left (hgne x hbt)
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [hgne b hb]
  linear_combination -hh

theorem b52_three_product_locally_exponential
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ℂ) {U : Set E} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hgne : ∀ x ∈ U, g x ≠ 0) (k : E) (C : ℂ)
    (hprod : ∀ x ∈ U, ∀ y ∈ U, k - x - y ∈ U → g x * g y * g (k - x - y) = C)
    (b t : E) (hb : b ∈ U) (ht : t ∈ U) (hbt : k - t - b ∈ U) :
    ∃ (L : E →L[ℂ] ℂ) (d : ℂ) (W : Set E), d ≠ 0 ∧
      IsOpen W ∧ W.Nonempty ∧ W ⊆ U ∧ ∀ x ∈ W, g x = d * Complex.exp (L x) := by
  letI := NormedSpace.restrictScalars ℝ ℂ E
  have hopen : IsOpen (U ∩ {x | k - x - b ∈ U}) :=
    hU.inter (hU.preimage ((continuous_const.sub continuous_id).sub continuous_const))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen t ⟨ht, hbt⟩
  let L := (g b)⁻¹ • fderiv ℂ g b
  let q : E → ℂ := fun x ↦ g x * Complex.exp (-(L x))
  have hqd : ∀ x ∈ Metric.ball t r, HasFDerivAt q (0 : E →L[ℂ] ℂ) x := by
    intro x hx
    have hd : HasFDerivAt g (g x • L) x := by
      rw [← b52_three_product_fderiv g hU hg hgne k C hprod b x hb
        (hball hx).1 (hball hx).2]
      exact (hg.differentiableAt (hU.mem_nhds (hball hx).1)).hasFDerivAt
    have he := hd.mul ((-L).hasFDerivAt.cexp)
    convert he using 1
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.zero_apply, smul_eq_mul]
    ring
  obtain ⟨d, hd⟩ := Metric.isOpen_ball.exists_is_const_of_fderiv_eq_zero
    (convex_ball t r).isPreconnected
    (fun x hx ↦ (hqd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hqd x hx).fderiv)
  have hdne : d ≠ 0 := by
    rw [← hd t (Metric.mem_ball_self hr)]
    exact mul_ne_zero (hgne t ht) (Complex.exp_ne_zero _)
  refine ⟨L, d, Metric.ball t r, hdne, Metric.isOpen_ball,
    ⟨t, Metric.mem_ball_self hr⟩, (fun x hx ↦ (hball hx).1), ?_⟩
  intro x hx
  have hh := hd x hx
  change g x * Complex.exp (-(L x)) = d at hh
  rw [Complex.exp_neg] at hh
  exact (div_eq_iff (Complex.exp_ne_zero (L x))).mp hh

end HodgeLean.Foundations.Program
