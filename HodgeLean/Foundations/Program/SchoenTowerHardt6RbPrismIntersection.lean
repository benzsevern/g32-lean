import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismPointWeights
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismComparison
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-! Common-face intersections of ordered variable-height prism simplices. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_prism_intersection_of_lt {E : Type*}
    [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (v : Fin (m + 1) → E) (hv : AffineIndependent ℝ v)
    (l u : Fin (m + 1) → ℝ) (hlu : ∀ i, l i ≤ u i)
    (j k : Fin (m + 1)) (hjk : j < k) :
    let S : Fin (m + 1) → Set (E × ℝ) := fun a =>
      ((fun i => (v i, l i)) '' {i | a ≤ i}) ∪
        ((fun i => (v i, u i)) '' {i | i ≤ a})
    convexHull ℝ (S j) ∩ convexHull ℝ (S k) = convexHull ℝ (S j ∩ S k) := by
  classical
  intro S
  apply Set.Subset.antisymm ?_
    (Set.subset_inter (convexHull_mono Set.inter_subset_left)
      (convexHull_mono Set.inter_subset_right))
  rintro p ⟨hpj, hpk⟩
  obtain ⟨lo, up, hpos, hsum, hbase, hheight, hlo, hup⟩ :=
    s2v_hardt6rb_prism_point_weights v l u j p hpj
  obtain ⟨lo', up', hpos', hsum', hbase', hheight', hlo', hup'⟩ :=
    s2v_hardt6rb_prism_point_weights v l u k p hpk
  have hmass (i) : lo i + up i = lo' i + up' i :=
    hv.eq_of_sum_eq_sum (hsum.trans hsum'.symm) (hbase.trans hbase'.symm)
      i (Finset.mem_univ i)
  have hcollapse := s2v_hardt6rb_prism_gap_collapse l u lo up lo' up' j k hjk
    hlu hpos hpos' hmass hup hlo' (hheight.trans hheight'.symm)
  have hdefault : (v j, u j) ∈ S j ∩ S k :=
    ⟨Or.inr ⟨j, by simp, rfl⟩, Or.inr ⟨j, by exact hjk.le, rfl⟩⟩
  have hlo_mem (i) (hne : lo i ≠ 0) : (v i, l i) ∈ S j ∩ S k := by
    have hji : j ≤ i := le_of_not_gt (fun hi => hne (hlo i hi))
    refine ⟨Or.inl ⟨i, hji, rfl⟩, ?_⟩
    by_cases hki : k ≤ i
    · exact Or.inl ⟨i, hki, rfl⟩
    · have hik : i < k := lt_of_not_ge hki
      have hgap : u i = l i :=
        sub_eq_zero.mp ((mul_eq_zero.mp (hcollapse i hik)).resolve_left hne)
      exact Or.inr ⟨i, hik.le, by simp only [hgap]⟩
  have hup_mem (i) (hne : up i ≠ 0) : (v i, u i) ∈ S j ∩ S k := by
    have hij : i ≤ j := le_of_not_gt (fun hi => hne (hup i hi))
    exact ⟨Or.inr ⟨i, hij, rfl⟩, Or.inr ⟨i, hij.trans hjk.le, rfl⟩⟩
  let zlo : Fin (m + 1) → E × ℝ := fun i =>
    if lo i = 0 then (v j, u j) else (v i, l i)
  let zup : Fin (m + 1) → E × ℝ := fun i =>
    if up i = 0 then (v j, u j) else (v i, u i)
  have hlo_eq (i) : lo i • zlo i = lo i • (v i, l i) := by
    by_cases hi : lo i = 0 <;> simp only [zlo, hi, ite_true, ite_false, zero_smul]
  have hup_eq (i) : up i • zup i = up i • (v i, u i) := by
    by_cases hi : up i = 0 <;> simp only [zup, hi, ite_true, ite_false, zero_smul]
  apply mem_convexHull_of_exists_fintype (Sum.elim lo up) (Sum.elim zlo zup)
  · intro i
    cases i with
    | inl i => exact (hpos i).1
    | inr i => exact (hpos i).2
  · rw [Fintype.sum_sum_type]
    simpa only [Sum.elim_inl, Sum.elim_inr, ← Finset.sum_add_distrib] using hsum
  · intro i
    cases i with
    | inl i =>
      dsimp only [Sum.elim_inl, zlo]
      split_ifs with hi
      · exact hdefault
      · exact hlo_mem i hi
    | inr i =>
      dsimp only [Sum.elim_inr, zup]
      split_ifs with hi
      · exact hdefault
      · exact hup_mem i hi
  · rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, hlo_eq, hup_eq]
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_sum]
      change (∑ i, lo i • v i) + (∑ i, up i • v i) = p.1
      rw [← Finset.sum_add_distrib]
      simpa only [← add_smul] using hbase
    · simp only [Prod.snd_add, Prod.snd_sum]
      change (∑ i, lo i * l i) + (∑ i, up i * u i) = p.2
      simpa only [Finset.sum_add_distrib] using hheight

theorem s2v_hardt6rb_prism_intersection {E : Type*}
    [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (v : Fin (m + 1) → E) (hv : AffineIndependent ℝ v)
    (l u : Fin (m + 1) → ℝ) (hlu : ∀ i, l i ≤ u i)
    (j k : Fin (m + 1)) :
    let S : Fin (m + 1) → Set (E × ℝ) := fun a =>
      ((fun i => (v i, l i)) '' {i | a ≤ i}) ∪
        ((fun i => (v i, u i)) '' {i | i ≤ a})
    convexHull ℝ (S j) ∩ convexHull ℝ (S k) = convexHull ℝ (S j ∩ S k) := by
  intro S
  rcases lt_trichotomy j k with h | h | h
  · exact s2v_hardt6rb_prism_intersection_of_lt v hv l u hlu j k h
  · subst k
    simp only [Set.inter_self]
  · simpa only [Set.inter_comm] using
      s2v_hardt6rb_prism_intersection_of_lt v hv l u hlu k j h

end HodgeLean.Foundations.Program
