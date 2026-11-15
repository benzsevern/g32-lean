import HodgeLean.Foundations.Program.SchoenTowerL1bMatrixCoordinates
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section
open scoped BigOperators
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Distinct evaluation values replace all low polynomial coefficients simultaneously. -/
theorem s2v_l1b_finite_evaluation_coordinates
    {K : Type*} [Field K] (n : ℕ) (a p : Fin n → K) (ha : Function.Injective a) :
    ∃ e : MvPolynomial (Fin n) K ≃ₐ[K] MvPolynomial (Fin n) K,
      ∀ i, e (X i) = (∑ j, C (a i ^ j.val) * X j) + C (p i) := by
  let M := Matrix.vandermonde a
  have hM : IsUnit M.det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr ha)
  exact s2v_l1b_matrix_affine_coordinates M M⁻¹
    (Matrix.mul_nonsing_inv _ hM) (Matrix.nonsing_inv_mul _ hM) p

/-- An etale coefficient map stays etale after replacing all coefficients by distinct affine evaluations. -/
theorem s2v_l1b_finite_evaluation_etale
    {K A : Type} [Field K] [CommRing A] (n : ℕ)
    (f : K →+* A) (z : Fin n → A) (a p : Fin n → K)
    (ha : Function.Injective a) (hEt : (eval₂Hom f z).Etale) :
    (eval₂Hom f (fun i => (∑ j, f (a i ^ j.val) * z j) + f (p i))).Etale := by
  obtain ⟨e, he⟩ := s2v_l1b_finite_evaluation_coordinates n a p ha
  have hcomp : (eval₂Hom f z).comp e.toRingEquiv.toRingHom =
      eval₂Hom f (fun i => (∑ j, f (a i ^ j.val) * z j) + f (p i)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, eval₂Hom_C]
      change eval₂Hom f z (e (C r)) = f r
      rw [show e (C r) = C r from e.commutes r, eval₂Hom_C]
    · intro i
      rw [RingHom.comp_apply, eval₂Hom_X']
      change eval₂Hom f z (e (X i)) = _
      rw [he]
      simp only [map_add, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X']
  rw [← hcomp]
  exact RingHom.Etale.stableUnderComposition e.toRingEquiv.toRingHom _
    (RingHom.Etale.of_bijective e.bijective) hEt

end HodgeLean.Foundations.Program
