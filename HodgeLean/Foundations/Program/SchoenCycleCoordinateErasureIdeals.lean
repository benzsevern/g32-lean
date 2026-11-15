import HodgeLean.Foundations.Program.SchoenCycleCoordinateErasureKernel
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # Coordinate ideals under marked-zero substitution -/
noncomputable section
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Marked-zero substitution maps the full coordinate ideal onto the moving
coordinate ideal over every coefficient ring.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1. -/
theorem s2e_eraseFirstCoordinate_coordinateIdeal
    (R : Type*) [CommRing R] (n : ℕ) :
    Ideal.map (s2e_eraseFirstCoordinate R n).toRingHom (idealOfVars (Fin (n + 1)) R) =
      idealOfVars (Fin n) R := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change s2e_eraseFirstCoordinate R n (X i) ∈ idealOfVars (Fin n) R
    change aeval (Fin.cases 0 MvPolynomial.X) (X i : MvPolynomial (Fin (n + 1)) R) ∈ _
    rw [aeval_X]
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Ideal.zero_mem _
    · exact Ideal.subset_span ⟨j, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hm := Ideal.mem_map_of_mem (s2e_eraseFirstCoordinate R n).toRingHom
      (Ideal.subset_span (s := Set.range (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R))
        ⟨j.succ, rfl⟩)
    change aeval (Fin.cases 0 MvPolynomial.X)
      (X j.succ : MvPolynomial (Fin (n + 1)) R) ∈ _ at hm
    rw [aeval_X] at hm
    exact hm

/-- At every finite total order, the substitution kernel is the sum of the
marked coordinate ideal and the full coordinate power ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 1 and 10. -/
theorem s2e_eraseFirstCoordinate_power_comap
    (R : Type*) [CommRing R] (n N : ℕ) :
    Ideal.comap (s2e_eraseFirstCoordinate R n).toRingHom (idealOfVars (Fin n) R ^ N) =
      idealOfVars (Fin (n + 1)) R ^ N ⊔
        Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) R)} := by
  have hm : Ideal.map (s2e_eraseFirstCoordinate R n).toRingHom
      (idealOfVars (Fin (n + 1)) R ^ N) = idealOfVars (Fin n) R ^ N := by
    rw [Ideal.map_pow, s2e_eraseFirstCoordinate_coordinateIdeal]
  have hs : Function.Surjective (s2e_eraseFirstCoordinate R n).toRingHom :=
    s2e_eraseFirstCoordinate_surjective R n
  rw [← hm, Ideal.comap_map_of_surjective (s2e_eraseFirstCoordinate R n).toRingHom hs,
    ← RingHom.ker_eq_comap_bot, s2e_eraseFirstCoordinate_kernel]

end HodgeLean.Foundations.Program
