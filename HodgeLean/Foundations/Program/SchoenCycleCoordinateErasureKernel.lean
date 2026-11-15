import HodgeLean.Foundations.Program.SchoenCycleCoordinateErasure
import Mathlib.RingTheory.Ideal.Maps

/-! # The actual polynomial ideal of marked-zero substitution -/
noncomputable section
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Marked-zero substitution has exactly the marked coordinate ideal as kernel
over every coefficient ring.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1. -/
theorem s2e_eraseFirstCoordinate_kernel
    (R : Type*) [CommRing R] (n : ℕ) :
    RingHom.ker (s2e_eraseFirstCoordinate R n).toRingHom =
      Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) R)} := by
  ext p
  change s2e_eraseFirstCoordinate R n p = 0 ↔ _
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hp
    obtain ⟨q, hq⟩ := s2e_eraseFirstCoordinate_decomposition R n p
    rw [hp, map_zero, zero_add] at hq
    exact ⟨q, hq⟩
  · rintro ⟨q, rfl⟩
    simp only [map_mul, s2e_eraseFirstCoordinate, aeval_X, Fin.cases_zero, zero_mul]

end HodgeLean.Foundations.Program
