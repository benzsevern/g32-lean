import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span

noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- An exact weighted principal-ideal power gives an actual unit equation
in any domain. Factoriality of the section ring is not required. -/
theorem s2e_c1_weighted_principal_unit
    {R J : Type*} [CommRing R] [IsDomain R] [Fintype J]
    (g : J → R) (n : J → ℕ) (E : R) (m : ℕ)
    (hI : (∏ j, (Ideal.span {g j}) ^ n j) = (Ideal.span {E}) ^ m) :
    ∃ u : Rˣ, (∏ j, g j ^ n j) = (u : R) * E ^ m := by
  have he : Ideal.span {∏ j, g j ^ n j} = Ideal.span {E ^ m} := by
    rw [← Ideal.prod_span_singleton]
    simpa only [← Ideal.span_singleton_pow] using hI
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp he.symm
  exact ⟨u, hu.symm.trans (mul_comm _ _)⟩

end HodgeLean.Foundations.Program
