import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.Ring

/-! # Polynomial coordinate ideals at actual scalar evaluations -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Subtracting a polynomial's scalar evaluation lies in the ideal generated
by the centered coordinate variables.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1. -/
theorem s2e_polynomial_sub_evaluation_mem
    (R σ : Type*) [CommRing R] (φ : MvPolynomial σ R →ₐ[R] R) (p : MvPolynomial σ R) :
    p - C (φ p) ∈ Ideal.span (Set.range fun i : σ => X i - C (φ (X i))) := by
  let I : Ideal (MvPolynomial σ R) := Ideal.span (Set.range fun i : σ => X i - C (φ (X i)))
  have hc (c : R) : φ (C c) = c := by
    simpa only [MvPolynomial.algebraMap_eq, Algebra.algebraMap_self, RingHom.id_apply] using φ.commutes c
  change p - C (φ p) ∈ I
  induction p using MvPolynomial.induction_on with
  | C c => simp only [hc, sub_self, Ideal.zero_mem]
  | add p q hp hq =>
    convert I.add_mem hp hq using 1 <;> simp only [map_add] <;> ring
  | mul_X p i hp =>
    have he : p * X i - C (φ (p * X i)) =
        (p - C (φ p)) * X i + C (φ p) * (X i - C (φ (X i))) := by
      rw [map_mul, map_mul]
      ring
    rw [he]
    exact I.add_mem (I.mul_mem_right (X i) hp)
      (I.mul_mem_left (C (φ p)) (Ideal.subset_span ⟨i, rfl⟩))

/-- Scalar polynomial evaluation has the centered coordinate ideal as its kernel.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1. -/
theorem s2e_polynomial_evaluation_kernel
    (R σ : Type*) [CommRing R] (φ : MvPolynomial σ R →ₐ[R] R) :
    RingHom.ker φ.toRingHom = Ideal.span (Set.range fun i : σ => X i - C (φ (X i))) := by
  have hc (c : R) : φ (C c) = c := by
    simpa only [MvPolynomial.algebraMap_eq, Algebra.algebraMap_self, RingHom.id_apply] using φ.commutes c
  apply le_antisymm
  · intro p hp
    have h0 : φ p = 0 := hp
    simpa only [h0, map_zero, sub_zero] using s2e_polynomial_sub_evaluation_mem R σ φ p
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    change φ (X i - C (φ (X i))) = 0
    rw [map_sub, hc, sub_self]

/-- For one variable the scalar evaluation kernel has its single centered
coordinate as generator.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1. -/
theorem s2e_one_variable_evaluation_kernel
    (R : Type*) [CommRing R] (φ : MvPolynomial (Fin 1) R →ₐ[R] R) :
    RingHom.ker φ.toRingHom = Ideal.span {X 0 - C (φ (X 0))} := by
  rw [s2e_polynomial_evaluation_kernel]
  have he : (fun i : Fin 1 => (X i : MvPolynomial (Fin 1) R) - C (φ (X i))) =
      (fun _ : Fin 1 => X 0 - C (φ (X 0))) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]
  rw [he, Set.range_const]

end HodgeLean.Foundations.Program
