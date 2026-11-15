import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Algebra.Basic

/-! Rescaling a field generator by a nonzero coefficient preserves generation. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

theorem field_generator_div_coefficient
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (v : K) (E : R) (hE : algebraMap R K E ≠ 0)
    (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤) :
    Subfield.closure (Set.range (algebraMap R K) ∪ {v / algebraMap R K E}) = ⊤ := by
  let T := Subfield.closure (Set.range (algebraMap R K) ∪ {v / algebraMap R K E})
  apply top_unique
  rw [← hgen]
  apply Subfield.closure_le.mpr
  rintro x (⟨r, rfl⟩ | hx)
  · exact Subfield.subset_closure (Or.inl ⟨r, rfl⟩)
  · rw [Set.mem_singleton_iff.mp hx]
    have hdiv : v / algebraMap R K E ∈ T :=
      Subfield.subset_closure (Or.inr rfl)
    have hcoeff : algebraMap R K E ∈ T := Subfield.subset_closure (Or.inl ⟨E, rfl⟩)
    simpa only [T, SetLike.mem_coe, div_mul_cancel₀ v hE] using T.mul_mem hdiv hcoeff

#print axioms field_generator_div_coefficient
end HodgeLean.Foundations.QuotientDuality
