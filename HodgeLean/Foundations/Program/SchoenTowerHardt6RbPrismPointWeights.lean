import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismCoordinates
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Supported lower and upper weights for points of an ordered prism simplex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_prism_point_weights {E : Type*}
    [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (v : Fin (m + 1) → E) (l u : Fin (m + 1) → ℝ) (j : Fin (m + 1))
    (p : E × ℝ) (hp : p ∈ convexHull ℝ
      (((fun i => (v i, l i)) '' {i | j ≤ i}) ∪
        ((fun i => (v i, u i)) '' {i | i ≤ j}))) :
    ∃ lo up : Fin (m + 1) → ℝ,
      (∀ i, 0 ≤ lo i ∧ 0 ≤ up i) ∧
      (∑ i, (lo i + up i)) = 1 ∧
      (∑ i, (lo i + up i) • v i) = p.1 ∧
      (∑ i, (lo i * l i + up i * u i)) = p.2 ∧
      (∀ i, i < j → lo i = 0) ∧ (∀ i, j < i → up i = 0) := by
  rw [← s2v_hardt6rb_prism_vertex_range v l u j] at hp
  obtain ⟨t, ht⟩ := (s2v_hardt6rb_convexHull_range_weights _ p).mp hp
  let lo : Fin (m + 1) → ℝ := fun i => if i < j then 0 else t.val (some i)
  let up : Fin (m + 1) → ℝ := fun i =>
    (if i < j then t.val (some i) else 0) + (if i = j then t.val none else 0)
  have hpair (i) : lo i + up i = t.val (some i) + if i = j then t.val none else 0 := by
    by_cases hi : i < j <;> simp only [lo, up, hi, ite_true, ite_false, zero_add, add_zero]
  have hheight (i) : lo i * l i + up i * u i =
      t.val (some i) * (if i < j then u i else l i) +
        if i = j then t.val none * u j else 0 := by
    by_cases heq : i = j
    · subst i
      simp only [lo, up, lt_self_iff_false, ite_false, ite_true, zero_add]
    · by_cases hi : i < j <;>
        simp only [lo, up, heq, hi, ite_true, ite_false, zero_add, add_zero, zero_mul]
  refine ⟨lo, up, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    constructor
    · dsimp only [lo]
      split_ifs
      · exact le_rfl
      · exact t.property.1 _
    · dsimp only [up]
      apply add_nonneg
      · split_ifs
        · exact t.property.1 _
        · exact le_rfl
      · split_ifs
        · exact t.property.1 _
        · exact le_rfl
  · simp only [hpair, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have htotal := t.property.2
    rw [Fintype.sum_option] at htotal
    linarith
  · have hf := congrArg Prod.fst ht
    simp only [Fintype.sum_option, Prod.fst_add, Prod.fst_sum] at hf
    change t.val none • v j + (∑ i, t.val (some i) • v i) = p.1 at hf
    simp only [hpair, add_smul, ite_smul, zero_smul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simpa only [add_comm] using hf
  · have hs := congrArg Prod.snd ht
    simp only [Fintype.sum_option, Prod.snd_add, Prod.snd_sum] at hs
    change t.val none * u j + (∑ i, t.val (some i) *
      (if i < j then u i else l i)) = p.2 at hs
    simp only [hheight, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    linarith
  · intro i hi
    simp only [lo, hi, ite_true]
  · intro i hi
    have hlt : ¬i < j := not_lt_of_ge hi.le
    have hne : i ≠ j := ne_of_gt hi
    simp only [up, hlt, hne, ite_false, zero_add]

end HodgeLean.Foundations.Program
