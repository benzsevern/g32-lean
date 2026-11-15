import HodgeLean.Foundations.Program.BraidBridgesPolynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace HodgeLean.Foundations.Program
open Polynomial

theorem b65x_polynomial_strictMono (p : ℚ[X]) (a b : ℝ)
    (h : ∀ t ∈ Set.Icc a b, 0 < p.derivative.eval₂ (Rat.castHom ℝ) t) :
    StrictMonoOn (fun t ↦ p.eval₂ (Rat.castHom ℝ) t) (Set.Icc a b) := by
  have he : (fun t ↦ p.eval₂ (Rat.castHom ℝ) t) =
      (fun t ↦ (p.map (Rat.castHom ℝ)).eval t) := by
    funext t
    rw [Polynomial.eval₂_eq_eval_map]
  rw [he]
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    (p.map (Rat.castHom ℝ)).continuous.continuousOn
  intro t ht
  rw [Polynomial.deriv, Polynomial.derivative_map, ← Polynomial.eval₂_eq_eval_map]
  exact h t (interior_subset ht)

theorem b65x_isolated_root (f : ℝ → ℝ) (a b l r : ℝ)
    (hab : a ≤ b) (hcont : ContinuousOn f (Set.Icc a b))
    (ha : f a < 0) (hb : 0 < f b)
    (hmono : StrictMonoOn f (Set.Icc l r))
    (hexclude : ∀ t ∈ Set.Icc a b, f t = 0 → t ∈ Set.Icc l r) :
    ∃! t, t ∈ Set.Icc a b ∧ f t = 0 := by
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc hab hcont ⟨ha.le, hb.le⟩
  refine ⟨t, ⟨ht, hzero⟩, ?_⟩
  intro s hs
  exact hmono.injOn (hexclude s hs.1 hs.2) (hexclude t ht hzero) (hs.2.trans hzero.symm)

theorem b65x_phi_homogeneous (N D : ℂ) (hD : D ≠ 0)
    (h1 : N - D ≠ 0) (h2 : N + 2 * D ≠ 0) :
    b65r_phi (N / D) =
      (N ^ 2 * (N - 3 * D) ^ 4) / ((N - D) ^ 3 * (N + 2 * D) ^ 3) := by
  have h1' : N / D - 1 ≠ 0 := by
    intro h
    apply h1
    have := (div_eq_one_iff_eq hD).mp (sub_eq_zero.mp h)
    exact sub_eq_zero.mpr this
  have h2' : N / D + 2 ≠ 0 := by
    intro h
    apply h2
    field_simp [hD] at h
    linear_combination h
  unfold b65r_phi
  field_simp [hD, h1, h2, h1', h2']
  <;> ring

theorem b65x_quotient_signs (U V : ℂ) (hV : V ≠ 0) (a : ℝ)
    (p q sx sy : ℝ) (hsx : 0 < sx) (hsy : 0 < sy)
    (hp : U.re * V.re + U.im * V.im - a * (V.re ^ 2 + V.im ^ 2) = sx * p)
    (hq : U.im * V.re - U.re * V.im = sy * q) :
    ((U / V).re = a ↔ p = 0) ∧
    ((U / V).re - a < 0 ↔ p < 0) ∧
    (0 < (U / V).re - a ↔ 0 < p) ∧
    ((U / V).im < 0 ↔ q < 0) ∧
    (0 < (U / V).im ↔ 0 < q) := by
  have hn : 0 < V.re ^ 2 + V.im ^ 2 := by
    have := Complex.normSq_pos.mpr hV
    simpa only [Complex.normSq_apply, pow_two] using this
  have hr : (U / V).re - a = sx * p / (V.re ^ 2 + V.im ^ 2) := by
    rw [Complex.div_re]
    simp only [Complex.normSq_apply, ← pow_two]
    rw [← hp]
    field_simp [ne_of_gt hn]
    <;> ring
  have hi : (U / V).im = sy * q / (V.re ^ 2 + V.im ^ 2) := by
    rw [Complex.div_im]
    simp only [Complex.normSq_apply, ← pow_two]
    rw [← hq]
    field_simp [ne_of_gt hn]
    <;> ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← sub_eq_zero, hr, div_eq_zero_iff]
    simp [ne_of_gt hn, ne_of_gt hsx]
  · rw [hr, div_lt_iff₀ hn, zero_mul]
    constructor <;> intro h <;> nlinarith
  · rw [hr, lt_div_iff₀ hn, zero_mul]
    constructor <;> intro h <;> nlinarith
  · rw [hi, div_lt_iff₀ hn, zero_mul]
    constructor <;> intro h <;> nlinarith
  · rw [hi, lt_div_iff₀ hn, zero_mul]
    constructor <;> intro h <;> nlinarith

end HodgeLean.Foundations.Program
