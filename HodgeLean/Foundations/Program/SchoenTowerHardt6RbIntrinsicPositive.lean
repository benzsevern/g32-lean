import HodgeLean.Foundations.Program.SchoenTowerHardt6RbIntrinsicExtension
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbFaceWeights
import Mathlib.Tactic.Abel

/-! All independent simplex coordinates of an intrinsic interior point are strictly positive. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_intrinsicInterior_weights_pos {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (v : ι → E) (hv : AffineIndependent ℝ v) (w : stdSimplex ℝ ι)
    (hx : (∑ j, w.val j • v j) ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range v))) :
    ∀ i, 0 < w.val i := by
  classical
  intro i
  by_contra hnot
  have hwi : w.val i = 0 := le_antisymm (le_of_not_gt hnot) (w.property.1 i)
  have hy : v i ∈ convexHull ℝ (Set.range v) := subset_convexHull ℝ _ (Set.mem_range_self i)
  obtain ⟨t, ht, hz⟩ := s2v_hardt6rb_intrinsicInterior_extend _ hx hy
  obtain ⟨u, hu⟩ := (s2v_hardt6rb_convexHull_range_weights v _).mp hz
  let a : ι → ℝ := fun j => (1 + t) * w.val j - if j = i then t else 0
  have hdelta : (∑ j : ι, if j = i then t else 0) = t := by simp
  have hasum : (∑ j, a j) = 1 := by
    simp only [a, Finset.sum_sub_distrib, ← Finset.mul_sum, w.property.2, mul_one, hdelta]
    ring
  have hdeltaV : (∑ j : ι, (if j = i then t else 0) • v j) = t • v i := by
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hap : (∑ j, a j • v j) = (∑ j, w.val j • v j) + t • ((∑ j, w.val j • v j) - v i) := by
    calc
      (∑ j, a j • v j) = (∑ j, ((1 + t) * w.val j) • v j) -
          (∑ j, (if j = i then t else 0) • v j) := by
        simp only [a, sub_smul, Finset.sum_sub_distrib]
      _ = (1 + t) • (∑ j, w.val j • v j) - t • v i := by
        rw [hdeltaV]
        simp only [mul_smul, Finset.smul_sum]
      _ = _ := by rw [add_smul, one_smul, smul_sub]; abel
  have hai := hv.eq_of_sum_eq_sum (hasum.trans u.property.2.symm) (hap.trans hu.symm) i (Finset.mem_univ i)
  have hn : 0 ≤ a i := by rw [hai]; exact u.property.1 i
  change 0 ≤ (1 + t) * w.val i - (if i = i then t else 0) at hn
  simp only [hwi, mul_zero, ite_true, zero_sub] at hn
  linarith

end HodgeLean.Foundations.Program
