import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.BigOperators.Field

/-! Normalization of barycentric mass on selected vertices.
HC no distance; AV milestone no distance. -/

noncomputable section
open scoped BigOperators
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- Retain selected barycentric coordinates and normalize their total mass to one. -/
def s2e_pair_faceNormalize {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (w : stdSimplex ℝ ι) (hw : 0 < ∑ i ∈ S, w.val i) :
    stdSimplex ℝ ι :=
  ⟨fun i => if i ∈ S then w.val i / (∑ j ∈ S, w.val j) else 0, by
    constructor
    · intro i
      dsimp only
      split_ifs
      · exact div_nonneg (w.property.1 i) hw.le
      · exact le_rfl
    · rw [Fintype.sum_ite_mem, ← Finset.sum_div]
      exact div_self (ne_of_gt hw)⟩

/-- Normalization gives zero at every unselected vertex. -/
theorem s2e_pair_faceNormalize_outside {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (w : stdSimplex ℝ ι) (hw : 0 < ∑ i ∈ S, w.val i)
    (i : ι) (hi : i ∉ S) : (s2e_pair_faceNormalize S w hw).val i = 0 := by
  exact ite_eq_right hi

/-- A barycentric point already supported on the selected vertices is fixed. -/
theorem s2e_pair_faceNormalize_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (w : stdSimplex ℝ ι) (hw : 0 < ∑ i ∈ S, w.val i)
    (hsupport : ∀ i, i ∉ S → w.val i = 0) : s2e_pair_faceNormalize S w hw = w := by
  have hsum : ∑ i ∈ S, w.val i = 1 := by
    rw [← w.property.2]
    exact Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hsupport i hi)
  apply Subtype.ext
  funext i
  change (if i ∈ S then w.val i / (∑ j ∈ S, w.val j) else 0) = w.val i
  rw [hsum]
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi, div_one]
  · rw [ite_eq_right hi, hsupport i hi]

/-- Normalization varies continuously wherever the selected total mass is positive. -/
def s2e_pair_faceNormalizeMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) :
    C({w : stdSimplex ℝ ι | 0 < ∑ i ∈ S, w.val i}, stdSimplex ℝ ι) where
  toFun w := s2e_pair_faceNormalize S w.val w.property
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    by_cases hi : i ∈ S
    · change Continuous (fun w : {w : stdSimplex ℝ ι | 0 < ∑ i ∈ S, w.val i} =>
        if i ∈ S then w.val.val i / (∑ j ∈ S, w.val.val j) else 0)
      simp only [ite_eq_left hi]
      have hc (j : ι) : Continuous
          (fun w : {w : stdSimplex ℝ ι | 0 < ∑ i ∈ S, w.val i} => w.val.val j) :=
        (continuous_apply j).comp (continuous_subtype_val.comp continuous_subtype_val)
      exact (hc i).div (continuous_finsetSum S (fun j _ => hc j))
        (fun w => ne_of_gt w.property)
    · change Continuous (fun w : {w : stdSimplex ℝ ι | 0 < ∑ i ∈ S, w.val i} =>
        if i ∈ S then w.val.val i / (∑ j ∈ S, w.val.val j) else 0)
      simp only [ite_eq_right hi]
      exact continuous_const

/-- Interpolation to the normalized face keeps the selected mass positive. -/
theorem s2e_pair_faceNormalize_segment_mass_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (w : stdSimplex ℝ ι) (hw : 0 < ∑ i ∈ S, w.val i)
    (t : unitInterval) :
    0 < ∑ i ∈ S, ((1 - (t : ℝ)) * w.val i +
      (t : ℝ) * (s2e_pair_faceNormalize S w hw).val i) := by
  have hsum : ∑ i ∈ S, (s2e_pair_faceNormalize S w hw).val i = 1 := by
    calc
      _ = ∑ i ∈ S, w.val i / (∑ j ∈ S, w.val j) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact ite_eq_left hi
      _ = 1 := by rw [← Finset.sum_div, div_self (ne_of_gt hw)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum, mul_one]
  by_cases ht : (t : ℝ) = 0
  · simpa only [ht, sub_zero, one_mul, add_zero] using hw
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr t.property.2) hw.le)
      (lt_of_le_of_ne t.property.1 (Ne.symm ht))

/-- Normalization gives selected vertices total mass one. -/
theorem s2e_pair_faceNormalize_selected_total {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (w : stdSimplex ℝ ι) (hw : 0 < ∑ i ∈ S, w.val i) :
    (∑ i ∈ S, (s2e_pair_faceNormalize S w hw).val i) = 1 := by
  calc
    _ = ∑ i ∈ S, w.val i / (∑ j ∈ S, w.val j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ite_eq_left hi
    _ = 1 := by rw [← Finset.sum_div, div_self (ne_of_gt hw)]

end Semialgebraic.CompatibleTriangulation.Helpers
