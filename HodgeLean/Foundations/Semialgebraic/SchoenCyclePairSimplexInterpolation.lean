import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairFaceNormalization

/-! Interpolation of finite barycentric weights.
HC no distance; AV milestone no distance. -/
noncomputable section
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- Interpolation of two barycentric points is again a barycentric point. -/
def s2e_pair_simplexInterpolate {ι : Type*} [Fintype ι]
    (w v : stdSimplex ℝ ι) (t : unitInterval) : stdSimplex ℝ ι :=
  ⟨fun i => (1 - (t : ℝ)) * w.val i + (t : ℝ) * v.val i, by
    constructor
    · intro i
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (w.property.1 i))
        (mul_nonneg t.property.1 (v.property.1 i))
    · change (∑ i, ((1 - (t : ℝ)) * w.val i + (t : ℝ) * v.val i)) = 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        w.property.2, v.property.2, mul_one, mul_one, sub_add_cancel]⟩

end Semialgebraic.CompatibleTriangulation.Helpers
