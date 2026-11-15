import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismCuts
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic.FieldSimp

/-! Barycentric weights for ordered simplices in a variable-height prism. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_prism_staircase_weights {m : ℕ}
    (w : stdSimplex ℝ (Fin (m + 1))) (δ : Fin (m + 1) → ℝ)
    (hδ : ∀ i, 0 ≤ δ i) {y : ℝ} (hy : 0 ≤ y)
    (hyδ : y ≤ ∑ i, w.val i * δ i) :
    ∃ j : Fin (m + 1), ∃ lo up : Fin (m + 1) → ℝ,
      (∀ i, 0 ≤ lo i ∧ 0 ≤ up i) ∧
      (∀ i, lo i + up i = w.val i) ∧
      (∀ i, i < j → lo i = 0) ∧
      (∀ i, j < i → up i = 0) ∧
      (∑ i, up i * δ i) = y := by
  obtain ⟨j, hjlo, hjhi⟩ := s2v_hardt6rb_prism_prefix_cut
    (fun i => w.val i * δ i) (fun i => mul_nonneg (w.property.1 i) (hδ i)) hy hyδ
  let r := y - ∑ i, if i < j then w.val i * δ i else 0
  have hr : 0 ≤ r := sub_nonneg.mpr hjlo
  have hrδ : r ≤ w.val j * δ j := by dsimp only [r]; linarith
  let t := r / δ j
  have ht : 0 ≤ t ∧ t ≤ w.val j := by
    refine ⟨div_nonneg hr (hδ j), ?_⟩
    by_cases hz : δ j = 0
    · simp only [t, hz, div_zero]
      exact w.property.1 j
    · exact (div_le_iff₀ (lt_of_le_of_ne (hδ j) (Ne.symm hz))).mpr hrδ
  have htδ : t * δ j = r := by
    by_cases hz : δ j = 0
    · have hr0 : r = 0 := by rw [hz, mul_zero] at hrδ; linarith
      simp only [t, hz, div_zero, mul_zero, hr0]
    · exact div_mul_cancel₀ r hz
  let up : Fin (m + 1) → ℝ := fun i =>
    (if i < j then w.val i else 0) + (if i = j then t else 0)
  have hup (i) : 0 ≤ up i ∧ up i ≤ w.val i := by
    by_cases hij : i < j
    · have hne : i ≠ j := ne_of_lt hij
      simp only [up, hij, hne, ite_true, ite_false, add_zero]
      exact ⟨w.property.1 i, le_rfl⟩
    · by_cases heq : i = j
      · subst i
        simpa only [up, lt_self_iff_false, ite_false, ite_true, zero_add] using ht
      · simp only [up, hij, heq, ite_false, zero_add]
        exact ⟨le_rfl, w.property.1 i⟩
  refine ⟨j, (fun i => w.val i - up i), up, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨sub_nonneg.mpr (hup i).2, (hup i).1⟩
  · intro i
    exact sub_add_cancel _ _
  · intro i hij
    simp only [up, hij, ne_of_lt hij, ite_true, ite_false, add_zero, sub_self]
  · intro i hji
    have hij : ¬i < j := not_lt_of_ge (le_of_lt hji)
    have hne : i ≠ j := ne_of_gt hji
    simp only [up, hij, hne, ite_false, zero_add]
  · have hs : (∑ i, up i * δ i) =
        (∑ i, if i < j then w.val i * δ i else 0) + t * δ j := by
      simp [up, add_mul, Finset.sum_add_distrib]
    rw [hs, htδ]
    dsimp only [r]
    ring

end HodgeLean.Foundations.Program
