import Mathlib.Algebra.Field.Subfield.Basic

/-! Rescaling by any nonzero element of the generated coefficient field. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

theorem field_generator_div_base_closure
    {K : Type*} [Field K] (S : Set K) (v a : K)
    (ha : a ∈ Subfield.closure S) (hne : a ≠ 0)
    (hgen : Subfield.closure (S ∪ {v}) = ⊤) :
    Subfield.closure (S ∪ {v / a}) = ⊤ := by
  let T := Subfield.closure (S ∪ {v / a})
  have hcoeff : a ∈ T := (Subfield.closure_mono Set.subset_union_left) ha
  apply top_unique
  rw [← hgen]
  apply Subfield.closure_le.mpr
  intro x hx
  rcases hx with hx | hx
  · exact Subfield.subset_closure (Or.inl hx)
  · rw [Set.mem_singleton_iff.mp hx]
    have hdiv : v / a ∈ T := Subfield.subset_closure (Or.inr rfl)
    simpa only [T, SetLike.mem_coe, div_mul_cancel₀ v hne] using T.mul_mem hdiv hcoeff

#print axioms field_generator_div_base_closure
end HodgeLean.Foundations.QuotientDuality
