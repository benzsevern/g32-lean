import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Equal prism heights force zero gaps at vertices passed between ordered pivots. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_prism_gap_collapse {m : ℕ}
    (l u lo up lo' up' : Fin (m + 1) → ℝ) (j k : Fin (m + 1))
    (hjk : j < k) (hlu : ∀ i, l i ≤ u i)
    (hpos : ∀ i, 0 ≤ lo i ∧ 0 ≤ up i)
    (hpos' : ∀ i, 0 ≤ lo' i ∧ 0 ≤ up' i)
    (hmass : ∀ i, lo i + up i = lo' i + up' i)
    (hup : ∀ i, j < i → up i = 0) (hlo' : ∀ i, i < k → lo' i = 0)
    (hheight : (∑ i, (lo i * l i + up i * u i)) =
      ∑ i, (lo' i * l i + up' i * u i)) :
    ∀ i, i < k → lo i * (u i - l i) = 0 := by
  have hnonneg (i) : 0 ≤ up' i - up i := by
    by_cases hi : i < k
    · have hm := hmass i
      rw [hlo' i hi, zero_add] at hm
      linarith [(hpos i).1]
    · have hu0 := hup i (lt_of_lt_of_le hjk (le_of_not_gt hi))
      rw [hu0, sub_zero]
      exact (hpos' i).2
  have hid (i) : (up' i - up i) * (u i - l i) =
      (lo' i * l i + up' i * u i) - (lo i * l i + up i * u i) := by
    have hlow : lo' i = lo i + up i - up' i := by linarith [hmass i]
    rw [hlow]
    ring
  have hsum : (∑ i, (up' i - up i) * (u i - l i)) = 0 := by
    simp only [hid, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hheight.symm
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin (m + 1)))) =>
      mul_nonneg (hnonneg i) (sub_nonneg.mpr (hlu i)))).mp hsum
  intro i hi
  have hm := hmass i
  rw [hlo' i hi, zero_add] at hm
  have he : up' i - up i = lo i := by linarith
  simpa only [he] using hz i (Finset.mem_univ i)

end HodgeLean.Foundations.Program
