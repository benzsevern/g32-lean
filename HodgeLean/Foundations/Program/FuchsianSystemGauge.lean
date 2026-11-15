import HodgeLean.Foundations.Program.FuchsianSystemDefs

noncomputable section
namespace HodgeLean.Foundations.Program

def b65f_gaugeCoeff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : E →L[ℂ] E) (b : ℕ → E →L[ℂ] E)
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T - (R * T - T * R))) : ℕ → E →L[ℂ] E
  | 0 => 1
  | n + 1 => (Equiv.ofBijective
      (fun T : E →L[ℂ] E ↦ ((n + 1 : ℕ) : ℂ) • T - (R * T - T * R))
      (hnr (n + 1) (Nat.succ_pos n))).symm
      (∑ i ∈ Finset.range (n + 1), b i * b65f_gaugeCoeff R b hnr (n - i))
termination_by n => n

theorem b65f_gaugeCoeff_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : E →L[ℂ] E) (b : ℕ → E →L[ℂ] E)
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T - (R * T - T * R))) :
    b65f_gaugeCoeff R b hnr 0 = 1 := by
  rw [b65f_gaugeCoeff]

theorem b65f_gaugeCoeff_recurrence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : E →L[ℂ] E) (b : ℕ → E →L[ℂ] E)
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T - (R * T - T * R))) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) • b65f_gaugeCoeff R b hnr (n + 1) -
      (R * b65f_gaugeCoeff R b hnr (n + 1) - b65f_gaugeCoeff R b hnr (n + 1) * R) =
        ∑ i ∈ Finset.range (n + 1), b i * b65f_gaugeCoeff R b hnr (n - i) := by
  let e := Equiv.ofBijective
    (fun T : E →L[ℂ] E ↦ ((n + 1 : ℕ) : ℂ) • T - (R * T - T * R))
    (hnr (n + 1) (Nat.succ_pos n))
  change e (b65f_gaugeCoeff R b hnr (n + 1)) = _
  rw [b65f_gaugeCoeff]
  exact e.apply_symm_apply _

theorem b65f_gaugeCoeff_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : E →L[ℂ] E) (b : ℕ → E →L[ℂ] E)
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T - (R * T - T * R)))
    (c : ℕ → E →L[ℂ] E) (hc0 : c 0 = 1)
    (hc : ∀ n : ℕ, ((n + 1 : ℕ) : ℂ) • c (n + 1) -
      (R * c (n + 1) - c (n + 1) * R) =
        ∑ i ∈ Finset.range (n + 1), b i * c (n - i)) :
    c = b65f_gaugeCoeff R b hnr := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact hc0.trans (b65f_gaugeCoeff_zero R b hnr).symm
    | succ n =>
      apply (hnr (n + 1) (Nat.succ_pos n)).injective
      dsimp only
      rw [hc n, b65f_gaugeCoeff_recurrence]
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih (n - i) (by omega)]

theorem b65f_commutator_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R T : E →L[ℂ] E) : ‖R * T - T * R‖ ≤ 2 * ‖R‖ * ‖T‖ := by
  calc
    ‖R * T - T * R‖ ≤ ‖R * T‖ + ‖T * R‖ := norm_sub_le _ _
    _ ≤ ‖R‖ * ‖T‖ + ‖T‖ * ‖R‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

theorem b65f_gaugeOperator_large_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R T : E →L[ℂ] E) (k : ℕ) (hk : 4 * ‖R‖ < (k : ℝ)) :
    ‖T‖ ≤ (2 / (k : ℝ)) * ‖(k : ℂ) • T - (R * T - T * R)‖ := by
  have hk0 : (0 : ℝ) < k := (by positivity : (0 : ℝ) ≤ 4 * ‖R‖).trans_lt hk
  have he : (k : ℂ) • T =
      ((k : ℂ) • T - (R * T - T * R)) + (R * T - T * R) := by abel
  have hn : (k : ℝ) * ‖T‖ ≤
      ‖(k : ℂ) • T - (R * T - T * R)‖ + 2 * ‖R‖ * ‖T‖ := by
    calc
      (k : ℝ) * ‖T‖ = ‖(k : ℂ) • T‖ := by simp only [norm_smul, Complex.norm_natCast]
      _ ≤ ‖(k : ℂ) • T - (R * T - T * R)‖ + ‖R * T - T * R‖ := by
        conv_lhs => rw [he]
        exact norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (b65f_commutator_norm_le R T)
  rw [div_mul_eq_mul_div, le_div_iff₀ hk0]
  nlinarith [norm_nonneg T, mul_nonneg (norm_nonneg T) (sub_nonneg.mpr hk.le)]

end HodgeLean.Foundations.Program
