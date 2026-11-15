import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Tactic.NormNum

/-! Centroids retain their full vertex support even under affine-span incidence. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_mem_affineSpan_iff {E ι : Type*}
    [AddCommGroup E] [Module ℝ E]
    (v : ι → E) (hv : AffineIndependent ℝ v)
    (T U : Finset ι) (hT : T.Nonempty) :
    T.centroid ℝ v ∈ affineSpan ℝ (v '' (↑U : Set ι)) ↔ T ⊆ U := by
  classical
  have hsum := T.sum_centroidWeights_eq_one_of_nonempty ℝ hT
  change T.affineCombination ℝ v (T.centroidWeights ℝ) ∈
    affineSpan ℝ (v '' (↑U : Set ι)) ↔ T ⊆ U
  constructor
  · intro hx i hi
    by_contra hnot
    have hz := hv.eq_zero_of_affineCombination_mem_affineSpan hsum hx hi hnot
    have hcard : (T.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Finset.card_pos.mpr hT)
    exact (inv_ne_zero hcard) hz
  · intro hTU
    exact affineCombination_mem_affineSpan_image hsum
      (fun i hi hnot => False.elim (hnot (hTU hi))) v

end HodgeLean.Foundations.Program
