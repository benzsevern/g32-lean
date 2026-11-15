import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-! Ordered cuts of the vertical mass in a simplex prism. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_prism_prefix_cut {m : ℕ} (q : Fin (m + 1) → ℝ)
    (hq : ∀ i, 0 ≤ q i) {y : ℝ} (hy : 0 ≤ y) (hyq : y ≤ ∑ i, q i) :
    ∃ j : Fin (m + 1),
      (∑ i, if i < j then q i else 0) ≤ y ∧
      y ≤ (∑ i, if i < j then q i else 0) + q j := by
  induction m generalizing y with
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · simpa using hy
    · simpa using hyq
  | succ m ih =>
    by_cases hfirst : y ≤ q 0
    · refine ⟨0, ?_, ?_⟩
      · simpa using hy
      · simpa using hfirst
    · have htail : y - q 0 ≤ ∑ i : Fin (m + 1), q i.succ := by
        rw [Fin.sum_univ_succ] at hyq
        linarith
      obtain ⟨j, hjlo, hjhi⟩ := ih (fun i => q i.succ) (fun i => hq i.succ)
        (by linarith) htail
      have hp : (∑ i : Fin (m + 2), if i < j.succ then q i else 0) =
          q 0 + ∑ i : Fin (m + 1), if i < j then q i.succ else 0 := by
        rw [Fin.sum_univ_succ]
        simp
      exact ⟨j.succ, by rw [hp]; linarith, by rw [hp]; linarith⟩

end HodgeLean.Foundations.Program
