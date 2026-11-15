module

public import HodgeLean.Foundations.Program.SchoenCycleS1i4RegularHelpers
import all Mathlib.Basic.Complex.Basic

public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s2e_tupleIndex_eq_single {m n : ℕ} (s : Fin n → Fin m) (i : Fin m) :
    s2e_tupleIndex s = Finsupp.single i n ↔ s = fun _ => i := by
  classical
  constructor
  · intro h
    funext j
    by_contra hj
    have hb : 1 ≤ s2e_tupleIndex s (s j) := by
      have hb := Finset.single_le_sum (f := fun l : Fin n => Finsupp.single (s l) 1 (s j))
        (fun l _ => Nat.zero_le _) (Finset.mem_univ j)
      simpa only [s2e_tupleIndex, Finsupp.finsetSum_apply, Finsupp.single_eq_same] using hb
    rw [h, Finsupp.single_eq_of_ne hj] at hb
    omega
  · rintro rfl
    ext j
    by_cases hj : i = j <;> simp [s2e_tupleIndex, Finsupp.finsetSum_apply, Finsupp.single_apply, hj]

theorem s2e_recovered_axis_coeff (m n : ℕ)
    (p : FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ) (i : Fin m) :
    MvPowerSeries.coeff (Finsupp.single i n) (s2e_recoveredSeries m p) =
      p n (fun _ => Pi.single i 1) := by
  classical
  have hc := s2e_recovered_layer_coeff m n p (Finsupp.single i n)
  simp only [Finsupp.degree_single, ite_true] at hc
  rw [← hc]
  simp only [s2e_multilinearPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    s2e_tupleIndex_eq_single]
  simp

end HodgeLean.Foundations.Program
