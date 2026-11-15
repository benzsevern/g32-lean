import HodgeLean.Foundations.Program.NumeratorJetRecurrence

/-! # Finite scalar Taylor convolutions -/

noncomputable section
open Set Metric Matrix Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- Factorials relate scalar series coefficients to iterated derivatives. -/
theorem b65e_factorial_mul_coeff {f : ℂ → ℂ} {P : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt f P 0) (n : ℕ) :
    (n.factorial : ℂ) * P.coeff n = iteratedDeriv n f 0 := by
  obtain ⟨r, hr⟩ := hP
  have h := hr.factorial_smul (1 : ℂ) n
  simpa only [FormalMultilinearSeries.coeff, Pi.one_def, nsmul_eq_mul, ← iteratedDeriv_eq_iteratedFDeriv] using h

/-- Multiplication of analytic scalar functions is finite convolution on coefficients. -/
theorem b65e_mul_coeff {f g : ℂ → ℂ}
    {P Q R : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt f P 0) (hQ : HasFPowerSeriesAt g Q 0)
    (hR : HasFPowerSeriesAt (fun θ ↦ f θ * g θ) R 0) (n : ℕ) :
    R.coeff n = ∑ i ∈ Finset.range (n + 1), P.coeff i * Q.coeff (n - i) := by
  apply mul_left_cancel₀ (show (n.factorial : ℂ) ≠ 0 by exact_mod_cast n.factorial_ne_zero)
  rw [b65e_factorial_mul_coeff hR]
  rw [iteratedDeriv_fun_mul hP.analyticAt.contDiffAt hQ.analyticAt.contDiffAt,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  have hc : (n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) =
      (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  rw [← b65e_factorial_mul_coeff hP i, ← b65e_factorial_mul_coeff hQ (n - i), ← hc]
  ring

/-- Finite summation commutes with taking scalar Taylor coefficients. -/
theorem b65e_sum_coeff {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    {P : ι → FormalMultilinearSeries ℂ ℂ ℂ} {R : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : ∀ i ∈ s, HasFPowerSeriesAt (f i) (P i) 0)
    (hR : HasFPowerSeriesAt (fun θ ↦ ∑ i ∈ s, f i θ) R 0) (n : ℕ) :
    R.coeff n = ∑ i ∈ s, (P i).coeff n := by
  apply mul_left_cancel₀ (show (n.factorial : ℂ) ≠ 0 by exact_mod_cast n.factorial_ne_zero)
  rw [b65e_factorial_mul_coeff hR,
    iteratedDeriv_fun_sum (fun i hi ↦ (hP i hi).analyticAt.contDiffAt), Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi ↦ (b65e_factorial_mul_coeff (hP i hi) n).symm

/-- Subtraction commutes with taking scalar Taylor coefficients. -/
theorem b65e_sub_coeff {f g : ℂ → ℂ}
    {P Q R : FormalMultilinearSeries ℂ ℂ ℂ}
    (hP : HasFPowerSeriesAt f P 0) (hQ : HasFPowerSeriesAt g Q 0)
    (hR : HasFPowerSeriesAt (fun θ ↦ f θ - g θ) R 0) (n : ℕ) :
    R.coeff n = P.coeff n - Q.coeff n := by
  have he := hR.eq_formalMultilinearSeries (hP.sub hQ)
  rw [he]
  rfl

end HodgeLean.Foundations.Program
