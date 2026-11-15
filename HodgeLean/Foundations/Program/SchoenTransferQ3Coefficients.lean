import HodgeLean.Foundations.Program.SchoenTransferDefs
import HodgeLean.Adapters.CycleClassFlatPullback

/-! Finite coefficient collection for the specified inverse-image cycle. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- Each coefficient of the weighted inverse-image cycle is the sum of all
prime contributions with their original input coefficients. -/
theorem s4_q3_flatPullback_coefficient
    {X W : Over (Spec ↧ℂ)} [CompactSpace W.left]
    (q : X ⟶ W) (z : AlgebraicCycle W.left ℚ) (p : X.left) :
    ccm3_flatPullback q.left z p =
      ∑ x ∈ z.finite_support.toFinset, z x * ccm3_flatPullbackPrime q.left x p := by
  classical
  have hsupport : Function.support (fun x : W.left =>
      (ccm3_flatPullbackPrime q.left x).mapRange (z x * ·) (mul_zero _)) ⊆
      z.support := by
    intro x hx
    by_contra hn
    have hz : z x = 0 := not_not.mp hn
    apply hx
    apply Function.locallyFinsuppWithin.ext
    intro y
    simp only [Function.locallyFinsuppWithin.mapRange_apply, hz, zero_mul]
    rfl
  rw [ccm3_flatPullback, finsum_eq_sum_of_support_subset _
    (fun x hx => z.finite_support.mem_toFinset.mpr (hsupport hx))]
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Function.locallyFinsuppWithin.mapRange_apply]

end HodgeLean.Foundations.Program
