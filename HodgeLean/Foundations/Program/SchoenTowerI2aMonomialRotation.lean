import HodgeLean.Foundations.Program.SchoenTowerI2aFieldHelpers
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Monomial generator action under a coordinate rotation
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Rotating one coordinate multiplies the monomial generator by the corresponding exponent power.
Source: Mathlib, Finset.prod_mul_distrib and Finset.prod_eq_single. -/
theorem s2v_i2a_monomial_rotation
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (n : ℕ) (W : Fin n → A) (U : A) (α : Fin n → ℕ) (j : Fin n) (t : R)
    (G : A ≃ₐ[R] A)
    (hW : ∀ k, G (W k) = if k = j then algebraMap R A t * W k else W k)
    (hU : G U = U) :
    G (U * ∏ k, W k ^ α k) = algebraMap R A (t ^ α j) * (U * ∏ k, W k ^ α k) := by
  have hfactor (k : Fin n) : G (W k ^ α k) =
      (if k = j then algebraMap R A t ^ α k else 1) * W k ^ α k := by
    rw [map_pow, hW]
    split_ifs
    · exact mul_pow _ _ _
    · exact (one_mul _).symm
  have hp : ∏ k, (if k = j then algebraMap R A t ^ α k else 1) =
      algebraMap R A t ^ α j := by
    rw [Finset.prod_eq_single j]
    · simp
    · intro k _ hkj
      simp only [if_neg hkj]
    · simp
  rw [map_mul, hU, map_prod]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, hp, map_pow]
  ac_rfl

end HodgeLean.Foundations.Program
