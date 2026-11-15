import Mathlib.RingTheory.Ideal.Operations

/-! Extracting the unit in a weighted identity of principal branch ideals. -/
noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

theorem weighted_principal_product_unit
    {R ι : Type*} [CommRing R] [IsDomain R] [Fintype ι]
    (f s : ι → R) (α : ι → ℕ) (E : R) (m : ℕ)
    (h : (∏ j, (Ideal.span {f j}) ^ α j) =
      (∏ j, (Ideal.span {s j}) ^ α j) * (Ideal.span {E}) ^ m) :
    ∃ ε : Rˣ, (∏ j, f j ^ α j) = (ε : R) * ((∏ j, s j ^ α j) * E ^ m) := by
  have he : Ideal.span {∏ j, f j ^ α j} =
      Ideal.span {((∏ j, s j ^ α j) * E ^ m)} := by
    simpa only [Ideal.span_singleton_pow, Ideal.prod_span_singleton,
      Ideal.span_singleton_mul_span_singleton] using h
  obtain ⟨ε, hε⟩ := (Ideal.span_singleton_eq_span_singleton.mp he).symm
  exact ⟨ε, by simpa only [mul_comm] using hε.symm⟩

#print axioms weighted_principal_product_unit
end HodgeLean.Foundations.QuotientDuality
