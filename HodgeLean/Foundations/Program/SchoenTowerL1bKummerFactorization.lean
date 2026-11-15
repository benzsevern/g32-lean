import HodgeLean.Foundations.Program.SchoenTowerL1bKummerCancellation
import Mathlib.RingTheory.Ideal.Operations

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Equality of the weighted branch ideals supplies a regular unit in the section factorization. -/
theorem s2v_l1b_unit_of_weighted_ideal_identity
    {R : Type*} [CommRing R] [IsDomain R]
    {J L : Type*} [Fintype J] [Fintype L]
    (g : J → R) (n : J → ℕ) (eE : L → R)
    (u v : R) (m α : ℕ)
    (hI : (∏ j, (Ideal.span {g j}) ^ n j) =
      Ideal.span {u} ^ α * Ideal.span {v} ^ (m - α) *
        (∏ j, Ideal.span {eE j}) ^ m) :
    ∃ δ : Rˣ, (∏ j, g j ^ n j) =
      (δ : R) * u ^ α * v ^ (m - α) * (∏ j, eE j) ^ m := by
  simp only [Ideal.span_singleton_pow, Ideal.prod_span_singleton,
    Ideal.span_singleton_mul_span_singleton] at hI
  obtain ⟨δ, hδ⟩ := (Ideal.span_singleton_eq_span_singleton.mp hI).symm
  refine ⟨δ, ?_⟩
  rw [← hδ]
  ring

end HodgeLean.Foundations.Program
