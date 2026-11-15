import Mathlib.Algebra.Field.Basic

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A multiplicative coordinate cocycle over a field is given by ratios relative to any base chart. -/
theorem n2b_coordinate_cocycle_eq_ratio {ι K : Type} [Field K]
    (r : ι → ι → K) (hself : ∀ a, r a a = 1)
    (hmul : ∀ a b c, r a b * r b c = r a c)
    (i a b : ι) : r a b = r a i / r b i := by
  have hb : r b i ≠ 0 := by
    intro hz
    have h := hmul b i b
    rw [hz, zero_mul, hself] at h
    exact zero_ne_one h
  exact (eq_div_iff hb).mpr (hmul a b i)

end HodgeLean.Foundations.Program
