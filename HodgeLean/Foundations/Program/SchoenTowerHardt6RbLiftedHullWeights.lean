import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismCoordinates
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-! Barycentric band coordinates from the convex hull of both lifted vertex layers. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_lifted_hull_weights {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (v : ι → E) (l u : ι → ℝ) (hlu : ∀ i, l i ≤ u i)
    (p : E × ℝ) (hp : p ∈ convexHull ℝ
      (Set.range (fun i => (v i, l i)) ∪ Set.range (fun i => (v i, u i)))) :
    ∃ w : stdSimplex ℝ ι, (∑ i, w.val i • v i) = p.1 ∧
      (∑ i, w.val i * l i) ≤ p.2 ∧ p.2 ≤ ∑ i, w.val i * u i := by
  rw [← Set.Sum.elim_range] at hp
  obtain ⟨a, ha⟩ := (s2v_hardt6rb_convexHull_range_weights _ p).mp hp
  let lo : ι → ℝ := fun i => a.val (Sum.inl i)
  let up : ι → ℝ := fun i => a.val (Sum.inr i)
  have hsum : (∑ i, (lo i + up i)) = 1 := by
    have h := a.property.2
    rw [Fintype.sum_sum_type] at h
    simpa only [lo, up, Finset.sum_add_distrib] using h
  rw [Fintype.sum_sum_type] at ha
  have hb := congrArg Prod.fst ha
  have hh := congrArg Prod.snd ha
  simp only [Prod.fst_add, Prod.fst_sum] at hb
  simp only [Prod.snd_add, Prod.snd_sum] at hh
  change (∑ i, lo i • v i) + (∑ i, up i • v i) = p.1 at hb
  change (∑ i, lo i * l i) + (∑ i, up i * u i) = p.2 at hh
  let w : stdSimplex ℝ ι :=
    ⟨(fun i => lo i + up i),
      (fun i => add_nonneg (a.property.1 (Sum.inl i)) (a.property.1 (Sum.inr i))), hsum⟩
  refine ⟨w, ?_, ?_, ?_⟩
  · simpa only [w, add_smul, Finset.sum_add_distrib] using hb
  · rw [← hh, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    change (lo i + up i) * l i ≤ lo i * l i + up i * u i
    have hup : 0 ≤ up i := a.property.1 (Sum.inr i)
    nlinarith [mul_nonneg hup (sub_nonneg.mpr (hlu i))]
  · rw [← hh, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    change lo i * l i + up i * u i ≤ (lo i + up i) * u i
    have hlo : 0 ≤ lo i := a.property.1 (Sum.inl i)
    nlinarith [mul_nonneg hlo (sub_nonneg.mpr (hlu i))]

end HodgeLean.Foundations.Program
