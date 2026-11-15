module

public import HodgeLean.Foundations.Program.SchoenCycleDivisionSeries
import all HodgeLean.Foundations.Program.SchoenCycleDivisionCoefficients

public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

def s2e_anisotropicDegree (d k : ℕ) (a : Fin (d + 1) →₀ ℕ) : ℕ :=
  ∑ i, (if i = Fin.last d then 1 else k + 1) * a i

theorem s2e_low_anisotropic_degree (d k : ℕ) (a : Fin (d + 1) →₀ ℕ)
    (ha : s2e_anisotropicDegree d k a ≤ k) :
    a = Finsupp.single (Fin.last d) (a (Fin.last d)) ∧ a (Fin.last d) ≤ k := by
  classical
  have hb (i) : (if i = Fin.last d then 1 else k + 1) * a i ≤
      s2e_anisotropicDegree d k a := by
    unfold s2e_anisotropicDegree
    exact Finset.single_le_sum (f := fun j => (if j = Fin.last d then 1 else k + 1) * a j)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  constructor
  · ext i
    by_cases hi : i = Fin.last d
    · subst i
      simp
    · rw [Finsupp.single_eq_of_ne hi]
      have hi' := (hb i).trans ha
      simp only [if_neg hi] at hi'
      nlinarith
  · have := (hb (Fin.last d)).trans ha
    simpa using this

theorem s2e_anisotropic_weight (d k : ℕ) (R : Fin (d + 1) → ℝ)
    (t : ℝ) (a : Fin (d + 1) →₀ ℕ) :
    s2e_divWeight d (fun i => R i * t ^ (if i = Fin.last d then 1 else k + 1)) a =
      s2e_divWeight d R a * t ^ s2e_anisotropicDegree d k a := by
  simp only [s2e_divWeight, mul_pow, ← pow_mul, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, s2e_anisotropicDegree]

theorem s2e_anisotropic_coefficient_bound (d k : ℕ) (R : Fin (d + 1) → ℝ)
    (hR : ∀ i, 0 < R i) (E : MvPowerSeries (Fin (d + 1)) ℂ)
    (haxis : ∀ j ≤ k, MvPowerSeries.coeff (Finsupp.single (Fin.last d) j) E = 0)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (a : Fin (d + 1) →₀ ℕ) :
    ‖MvPowerSeries.coeff a E‖ *
        s2e_divWeight d (fun i => R i * t ^ (if i = Fin.last d then 1 else k + 1)) a ≤
      (‖MvPowerSeries.coeff a E‖ * s2e_divWeight d R a) * t ^ (k + 1) := by
  classical
  by_cases ha : s2e_anisotropicDegree d k a ≤ k
  · obtain ⟨heq, hj⟩ := s2e_low_anisotropic_degree d k a ha
    have hc : MvPowerSeries.coeff a E = 0 := heq ▸ haxis _ hj
    simp only [hc, norm_zero, zero_mul, le_refl]
  · rw [s2e_anisotropic_weight, ← mul_assoc]
    apply mul_le_mul_of_nonneg_left
    · exact pow_le_pow_of_le_one ht ht1 (by omega)
    · exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => (pow_pos (hR i) _).le)

theorem s2e_anisotropic_norm_bound (d k : ℕ) (R : Fin (d + 1) → ℝ)
    (hR : ∀ i, 0 < R i) (E : MvPowerSeries (Fin (d + 1)) ℂ)
    (hE : Summable (fun a => ‖MvPowerSeries.coeff a E‖ * s2e_divWeight d R a))
    (haxis : ∀ j ≤ k, MvPowerSeries.coeff (Finsupp.single (Fin.last d) j) E = 0)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Summable (fun a => ‖MvPowerSeries.coeff a E‖ *
      s2e_divWeight d (fun i => R i * t ^ (if i = Fin.last d then 1 else k + 1)) a) ∧
    s2e_divNorm d (fun i => R i * t ^ (if i = Fin.last d then 1 else k + 1)) E ≤
      s2e_divNorm d R E * t ^ (k + 1) := by
  have hs := hE.mul_right (t ^ (k + 1))
  have hb := s2e_anisotropic_coefficient_bound d k R hR E haxis t ht ht1
  have hn (a : Fin (d + 1) →₀ ℕ) : 0 ≤ ‖MvPowerSeries.coeff a E‖ *
      s2e_divWeight d (fun i => R i * t ^ (if i = Fin.last d then 1 else k + 1)) a :=
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ =>
      pow_nonneg (mul_nonneg (hR i).le (pow_nonneg ht _)) _)
  have hm := hs.of_nonneg_of_le hn hb
  refine ⟨hm, ?_⟩
  unfold s2e_divNorm
  rw [← tsum_mul_right]
  exact hm.tsum_le_tsum hb hs

end HodgeLean.Foundations.Program
