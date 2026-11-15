import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic.Ring

/-! # Polynomial substitution of a marked zero coordinate -/
noncomputable section
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Substitute zero for the first variable and retain all successor variables.
Source: Mathlib, MvPolynomial.aeval. -/
def s2e_eraseFirstCoordinate (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval (Fin.cases 0 MvPolynomial.X)

/-- A polynomial differs from its marked-zero substitution by a multiple of
the marked variable over every coefficient ring.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1. -/
theorem s2e_eraseFirstCoordinate_decomposition
    (R : Type*) [CommRing R] (n : ℕ) (p : MvPolynomial (Fin (n + 1)) R) :
    ∃ q, p = rename Fin.succ (s2e_eraseFirstCoordinate R n p) + X 0 * q := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, ?_⟩
    simp [s2e_eraseFirstCoordinate, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    obtain ⟨u, hu⟩ := hp
    obtain ⟨v, hv⟩ := hq
    refine ⟨u + v, ?_⟩
    calc
      p + q = (rename Fin.succ (s2e_eraseFirstCoordinate R n p) + X 0 * u) +
          (rename Fin.succ (s2e_eraseFirstCoordinate R n q) + X 0 * v) := congrArg₂ (· + ·) hu hv
      _ = _ := by simp only [map_add]; ring
  | mul_X p i hp =>
    refine Fin.cases ?_ (fun j => ?_) i
    · refine ⟨p, ?_⟩
      simp only [map_mul, s2e_eraseFirstCoordinate, aeval_X, Fin.cases_zero,
        mul_zero, map_zero, zero_add]
      exact mul_comm _ _
    · obtain ⟨q, hq⟩ := hp
      refine ⟨q * X j.succ, ?_⟩
      calc
        p * X j.succ =
            (rename Fin.succ (s2e_eraseFirstCoordinate R n p) + X 0 * q) * X j.succ :=
          congrArg (fun w => w * X j.succ) hq
        _ = _ := by
          simp only [map_mul, s2e_eraseFirstCoordinate, aeval_X, Fin.cases_succ, rename_X]
          ring

/-- Renaming all variables as successor coordinates splits marked-zero substitution.
Source: Mathlib, MvPolynomial.rename_X and MvPolynomial.aeval_X. -/
theorem s2e_eraseFirstCoordinate_rename_succ
    (R : Type*) [CommRing R] (n : ℕ) :
    (s2e_eraseFirstCoordinate R n).comp (rename Fin.succ) =
      AlgHom.id R (MvPolynomial (Fin n) R) := by
  apply MvPolynomial.algHom_ext
  intro i
  change s2e_eraseFirstCoordinate R n (rename Fin.succ (X i : MvPolynomial (Fin n) R)) = X i
  rw [rename_X]
  change aeval (Fin.cases 0 MvPolynomial.X) (X i.succ : MvPolynomial (Fin (n + 1)) R) = X i
  rw [aeval_X]
  rfl

/-- Marked-zero substitution is surjective over every coefficient ring.
Source: Mathlib, MvPolynomial.rename_X and MvPolynomial.aeval_X. -/
theorem s2e_eraseFirstCoordinate_surjective
    (R : Type*) [CommRing R] (n : ℕ) :
    Function.Surjective (s2e_eraseFirstCoordinate R n) := by
  intro p
  refine ⟨rename Fin.succ p, ?_⟩
  exact congrArg (fun f : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R => f p)
    (s2e_eraseFirstCoordinate_rename_succ R n)

/-- Evaluation after marked-zero substitution is evaluation on the tuple with
marked coordinate zero.
Source: Mathlib, MvPolynomial.algHom_ext and MvPolynomial.aeval_X. -/
theorem s2e_eraseFirstCoordinate_aeval
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (n : ℕ) (v : Fin n → A) (p : MvPolynomial (Fin (n + 1)) R) :
    aeval v (s2e_eraseFirstCoordinate R n p) = aeval (Fin.cases 0 v) p := by
  have he : (aeval v).comp (s2e_eraseFirstCoordinate R n) = aeval (Fin.cases 0 v) := by
    apply MvPolynomial.algHom_ext
    intro i
    change aeval v (s2e_eraseFirstCoordinate R n (X i : MvPolynomial (Fin (n + 1)) R)) =
      aeval (Fin.cases 0 v) (X i : MvPolynomial (Fin (n + 1)) R)
    rw [aeval_X]
    refine Fin.cases ?_ (fun j => ?_) i
    · change aeval v (aeval (Fin.cases 0 MvPolynomial.X)
        (X 0 : MvPolynomial (Fin (n + 1)) R)) = 0
      rw [aeval_X]
      exact map_zero _
    · change aeval v (aeval (Fin.cases 0 MvPolynomial.X)
        (X j.succ : MvPolynomial (Fin (n + 1)) R)) = v j
      rw [aeval_X]
      exact aeval_X v j
  exact congrArg (fun f : MvPolynomial (Fin (n + 1)) R →ₐ[R] A => f p) he

end HodgeLean.Foundations.Program
