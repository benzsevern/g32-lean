import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Option
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Tactic.Linarith

/-! Independence of a lifted simplex with one extra vertical vertex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_vertical_vertex_independent {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (v : ι → E) (hv : AffineIndependent ℝ v) (h : ι → ℝ) (j : ι)
    (k : ℝ) (hk : k ≠ h j) :
    AffineIndependent ℝ (fun o : Option ι =>
      o.elim (v j, k) (fun i => (v i, h i))) := by
  classical
  rw [affineIndependent_iff_of_fintype]
  intro w hw hwp
  have hp : (∑ o : Option ι, w o • o.elim (v j, k) (fun i => (v i, h i))) = 0 := by
    simpa only [Finset.weightedVSub_eq_linear_combination _ hw] using hwp
  have hfst := congrArg Prod.fst hp
  simp only [Fintype.sum_option, Prod.fst_add, Prod.fst_sum] at hfst
  change w none • v j + (∑ i, w (some i) • v i) = 0 at hfst
  let c : ι → ℝ := fun i => w (some i) + if i = j then w none else 0
  have hcs : (∑ i, c i) = 0 := by
    simp only [c, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Fintype.sum_option] at hw
    linarith
  have hcv : (∑ i, c i • v i) = 0 := by
    simp only [c, add_smul, ite_smul, zero_smul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simpa only [add_comm] using hfst
  have hc (i) : c i = 0 := hv.eq_zero_of_sum_eq_zero hcs hcv i (Finset.mem_univ i)
  have hb (i) : w (some i) = if i = j then -w none else 0 := by
    have hi := hc i
    dsimp only [c] at hi
    by_cases hij : i = j
    · subst i
      simp only [ite_true] at hi ⊢
      linarith
    · simp only [hij, ite_false, add_zero] at hi ⊢
      exact hi
  have hsnd := congrArg Prod.snd hp
  simp only [Fintype.sum_option, Prod.snd_add, Prod.snd_sum] at hsnd
  change w none * k + (∑ i, w (some i) * h i) = 0 at hsnd
  simp_rw [hb] at hsnd
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsnd
  have hn : w none = 0 := by
    have hm : w none * (k - h j) = 0 := by nlinarith [hsnd]
    exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hk)
  intro o
  cases o with
  | none => exact hn
  | some i => simp only [hb, hn, neg_zero, ite_self]

end HodgeLean.Foundations.Program
