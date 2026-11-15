import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismCoordinates
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! A positive finite convex combination contains a positive share of every other convex combination. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_positive_weights_split {ι : Type*} [Fintype ι]
    (w u : stdSimplex ℝ ι) (hw : ∀ i, 0 < w.val i) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ z : stdSimplex ℝ ι,
      ∀ i, w.val i = t * u.val i + (1 - t) * z.val i := by
  classical
  let S : Finset ℝ := insert 1 (Finset.univ.image w.val)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  let m := S.min' hS
  have hm : 0 < m := by
    change 0 < S.min' hS
    have hmem := S.min'_mem hS
    rcases Finset.mem_insert.mp hmem with h | h
    · rw [h]
      exact zero_lt_one
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      rw [← hi]
      exact hw i
  have hm1 : m ≤ 1 := S.min'_le _ (Finset.mem_insert_self _ _)
  have hmw (i : ι) : m ≤ w.val i :=
    S.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  let t := m / 2
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩
  have htw (i : ι) : t ≤ w.val i := by dsimp only [t]; linarith [hmw i]
  have hu1 (i : ι) : u.val i ≤ 1 := by
    rw [← u.property.2]
    exact Finset.single_le_sum (fun j _ => u.property.1 j) (Finset.mem_univ i)
  have hn (i : ι) : 0 ≤ w.val i - t * u.val i := by
    have hmuli : t * u.val i ≤ t := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hu1 i) ht.1.le
    linarith [htw i]
  have hd : 0 < 1 - t := sub_pos.mpr ht.2
  let z : stdSimplex ℝ ι :=
    ⟨(fun i => (w.val i - t * u.val i) / (1 - t)),
      (fun i => div_nonneg (hn i) hd.le), by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, w.property.2, u.property.2,
          mul_one, mul_inv_cancel₀ hd.ne']⟩
  refine ⟨t, ht, z, ?_⟩
  intro i
  change w.val i = t * u.val i + (1 - t) * ((w.val i - t * u.val i) / (1 - t))
  rw [mul_div_cancel₀ _ hd.ne']
  ring

end HodgeLean.Foundations.Program
