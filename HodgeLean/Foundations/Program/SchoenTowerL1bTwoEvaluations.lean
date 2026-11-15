import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.RingHom.Etale

/-! # Two distinct evaluations as coefficient coordinates
An affine coordinate change isolates the two low coefficients.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
namespace HodgeLean.Foundations.Program
universe u

/-- Two affine evaluations with invertible difference form a polynomial coordinate system. -/
theorem s2v_l1b_two_evaluation_coordinates {R : Type*} [CommRing R]
    (a b p q : R) (hab : IsUnit (b - a)) :
    ∃ e : MvPolynomial (Fin 2) R ≃ₐ[R] MvPolynomial (Fin 2) R,
      e (X 0) = X 0 + C a * X 1 + C p ∧
      e (X 1) = X 0 + C b * X 1 + C q := by
  obtain ⟨u, hu⟩ := hab
  have hb : b = a + (u : R) := by rw [hu]; ring
  rw [hb]
  let P := MvPolynomial (Fin 2) R
  let L₀ : P := X 0 + C a * X 1 + C p
  let L₁ : P := X 0 + C (a + (u : R)) * X 1 + C q
  let Y₁ : P := C (↑(u⁻¹) : R) * (X 1 - X 0 - C (q - p))
  let Y₀ : P := X 0 - C a * Y₁ - C p
  let F : P →ₐ[R] P := aeval ![L₀, L₁]
  let G : P →ₐ[R] P := aeval ![Y₀, Y₁]
  have hc : (C (u : R) : P) * C (↑(u⁻¹) : R) = 1 := by
    rw [← map_mul]
    simp only [Units.mul_inv, map_one]
  have hF0 : F (X 0) = L₀ := by
    exact MvPolynomial.aeval_X ![L₀, L₁] 0
  have hF1 : F (X 1) = L₁ := by
    exact MvPolynomial.aeval_X ![L₀, L₁] 1
  have hG0 : G (X 0) = Y₀ := by
    exact MvPolynomial.aeval_X ![Y₀, Y₁] 0
  have hG1 : G (X 1) = Y₁ := by
    exact MvPolynomial.aeval_X ![Y₀, Y₁] 1
  have hFC (c : R) : F (C c) = C c := F.commutes c
  have hGC (c : R) : G (C c) = C c := G.commutes c
  have hFG : F.comp G = AlgHom.id R P := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · change F (G (X 0)) = X 0
      rw [hG0]
      simp only [Y₀, Y₁, map_sub, map_mul, hFC, hF0, hF1, L₀, L₁, map_add]
      linear_combination -(C a * (X 1 : P)) * hc
    · change F (G (X 1)) = X 1
      rw [hG1]
      simp only [Y₁, map_sub, map_mul, hFC, hF0, hF1, L₀, L₁, map_add]
      linear_combination (X 1 : P) * hc
  have hGF : G.comp F = AlgHom.id R P := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · change G (F (X 0)) = X 0
      rw [hF0]
      simp only [L₀, map_add, map_mul, hGC, hG0, hG1, Y₀, Y₁]
      ring
    · change G (F (X 1)) = X 1
      rw [hF1]
      simp only [L₁, map_add, map_mul, hGC, hG0, hG1, Y₀, Y₁, map_sub]
      linear_combination ((X 1 : P) - X 0 - (C q - C p)) * hc
  exact ⟨AlgEquiv.ofAlgHom F G hFG hGF, hF0, hF1⟩

/-- The two-evaluation coordinate change preserves etaleness of the actual evaluation map. -/
theorem s2v_l1b_two_evaluation_etale {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (x₀ x₁ : A) (a b p q : R) (hab : IsUnit (b - a))
    (hE : (MvPolynomial.eval₂Hom f ![x₀, x₁]).Etale) :
    (MvPolynomial.eval₂Hom f
      ![x₀ + f a * x₁ + f p, x₀ + f b * x₁ + f q]).Etale := by
  obtain ⟨e, he₀, he₁⟩ := s2v_l1b_two_evaluation_coordinates a b p q hab
  let E := MvPolynomial.eval₂Hom f ![x₀, x₁]
  have hcomp : (E.comp e.toRingEquiv.toRingHom).Etale :=
    RingHom.Etale.stableUnderComposition e.toRingEquiv.toRingHom E
      (RingHom.Etale.of_bijective e.bijective) hE
  have heq : E.comp e.toRingEquiv.toRingHom = MvPolynomial.eval₂Hom f
      ![x₀ + f a * x₁ + f p, x₀ + f b * x₁ + f q] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      change E (e (C c)) = f c
      rw [show e (C c) = C c from e.commutes c]
      exact MvPolynomial.eval₂_C _ _ _
    · intro i
      simp only [RingHom.comp_apply]
      fin_cases i
      · change E (e (X 0)) = (MvPolynomial.eval₂Hom f
          ![x₀ + f a * x₁ + f p, x₀ + f b * x₁ + f q]) (X 0)
        rw [MvPolynomial.eval₂Hom_X']
        change E (e (X 0)) = x₀ + f a * x₁ + f p
        rw [he₀]
        simp only [E, map_add, map_mul, MvPolynomial.eval₂Hom_X',
          MvPolynomial.eval₂Hom_C, Matrix.cons_val_zero, Matrix.cons_val_one]
      · change E (e (X 1)) = (MvPolynomial.eval₂Hom f
          ![x₀ + f a * x₁ + f p, x₀ + f b * x₁ + f q]) (X 1)
        rw [MvPolynomial.eval₂Hom_X']
        change E (e (X 1)) = x₀ + f b * x₁ + f q
        rw [he₁]
        simp only [E, map_add, map_mul, MvPolynomial.eval₂Hom_X',
          MvPolynomial.eval₂Hom_C, Matrix.cons_val_zero, Matrix.cons_val_one]
  rwa [heq] at hcomp

end HodgeLean.Foundations.Program
