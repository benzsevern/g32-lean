module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Real

public section
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s2e_summable_convolution_majorant
    {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]
    (u v w : A → ℝ) (hu : Summable u) (hv : Summable v)
    (hu0 : ∀ a, 0 ≤ u a) (hv0 : ∀ a, 0 ≤ v a) (hw0 : ∀ a, 0 ≤ w a)
    (hw : ∀ a, w a ≤ ∑ p ∈ Finset.antidiagonal a, u p.1 * v p.2) :
    Summable w ∧ (∑' a, w a) ≤ (∑' a, u a) * (∑' a, v a) := by
  classical
  have hp := hu.mul_of_nonneg hv hu0 hv0
  have hs := summable_sum_mul_antidiagonal_of_summable_mul hp
  have hm := hs.of_nonneg_of_le hw0 hw
  refine ⟨hm, ?_⟩
  rw [hu.tsum_mul_tsum_eq_tsum_sum_antidiagonal hv hp]
  exact hm.tsum_le_tsum hw hs

end HodgeLean.Foundations.Program
