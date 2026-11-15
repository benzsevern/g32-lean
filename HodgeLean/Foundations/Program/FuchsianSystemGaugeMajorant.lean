import HodgeLean.Foundations.Program.FuchsianSystemGaugeBounds
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b65f_gaugeCoeff_geometric_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : E →L[ℂ] E) (b : ℕ → E →L[ℂ] E)
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T - (R * T - T * R)))
    (C M S : ℝ) (hC : 1 ≤ C) (hM : 0 ≤ M) (hS : 0 ≤ S)
    (hinv : ∀ k : ℕ, 0 < k → ∀ T : E →L[ℂ] E,
      ‖T‖ ≤ C * ‖(k : ℂ) • T - (R * T - T * R)‖)
    (hb : ∀ n, ‖b n‖ ≤ M * S ^ n) (n : ℕ) :
    ‖b65f_gaugeCoeff R b hnr n‖ ≤ (S + C * M) ^ n := by
  let D := S + C * M
  have hC0 : 0 ≤ C := by linarith
  have hD : 0 ≤ D := by positivity
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      rw [b65f_gaugeCoeff_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ n =>
      have hh := hinv (n + 1) (Nat.succ_pos n) (b65f_gaugeCoeff R b hnr (n + 1))
      rw [b65f_gaugeCoeff_recurrence] at hh
      calc
        ‖b65f_gaugeCoeff R b hnr (n + 1)‖ ≤
            C * ‖∑ i ∈ Finset.range (n + 1), b i * b65f_gaugeCoeff R b hnr (n - i)‖ := hh
        _ ≤ C * ∑ i ∈ Finset.range (n + 1), ‖b i * b65f_gaugeCoeff R b hnr (n - i)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) hC0
        _ ≤ C * ∑ i ∈ Finset.range (n + 1), (M * S ^ i) * D ^ (n - i) := by
          gcongr with i hi
          exact (norm_mul_le _ _).trans (mul_le_mul (hb i) (ih (n - i) (by omega))
            (norm_nonneg _) (by positivity))
        _ = (D - S) * ∑ i ∈ Finset.range (n + 1), S ^ i * D ^ (n - i) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          dsimp [D]
          ring
        _ = D ^ (n + 1) - S ^ (n + 1) := by
          simpa only [Nat.add_sub_cancel] using (Commute.all S D).mul_neg_geom_sum₂ (n + 1)
        _ ≤ D ^ (n + 1) := sub_le_self _ (by positivity)

theorem b65f_gaugeCoeff_summable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    (R : E →L[ℂ] E) (b : ℕ → E →L[ℂ] E)
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T - (R * T - T * R)))
    (C M S : ℝ) (hC : 1 ≤ C) (hM : 0 ≤ M) (hS : 0 ≤ S)
    (hinv : ∀ k : ℕ, 0 < k → ∀ T : E →L[ℂ] E,
      ‖T‖ ≤ C * ‖(k : ℂ) • T - (R * T - T * R)‖)
    (hb : ∀ n, ‖b n‖ ≤ M * S ^ n) (z : ℂ)
    (hz : ‖z‖ * (S + C * M) < 1) :
    Summable (fun n ↦ z ^ n • b65f_gaugeCoeff R b hnr n) := by
  have hD : 0 ≤ S + C * M := by positivity
  apply (summable_geometric_of_lt_one (mul_nonneg (norm_nonneg z) hD) hz).of_norm_bounded
  intro n
  rw [norm_smul, norm_pow, mul_pow]
  exact mul_le_mul_of_nonneg_left (b65f_gaugeCoeff_geometric_bound R b hnr C M S hC hM hS hinv hb n)
    (by positivity)

end HodgeLean.Foundations.Program
