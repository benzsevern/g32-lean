import HodgeLean.Foundations.Program.G32Native.AbelCollisionRoots
import Mathlib.FieldTheory.KummerExtension

/-! # Polynomial equations of the retained collision paths -/
noncomputable section
set_option maxHeartbeats 400000
open Polynomial
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- The tuple for one monic coefficient keeps its zero roots and its rotating roots. -/
def collisionRootTuple (j n : ℕ) (ζ t : ℂ) : Fin (j + n) → ℂ :=
  Fin.append (fun _ : Fin j => 0) (fun i : Fin n => ζ ^ i.val * t)

/-- The root tuple has exactly one varying lower monic coefficient, even at the collision. -/
theorem collisionRootTuple_polynomial (j : ℕ) {n : ℕ} (hn : 0 < n)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (t : ℂ) :
    (∏ i : Fin (j + n), (X - C (collisionRootTuple j n ζ t i))) =
      X ^ (j + n) + C (-(t ^ n)) * X ^ j := by
  rw [Fin.prod_univ_add]
  simp only [collisionRootTuple, Fin.append_left, Fin.append_right, map_zero, sub_zero,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have he : (∏ i : Fin n, (X - C (ζ ^ i.val * t))) = X ^ n - C (t ^ n) := by
    exact (Fin.prod_univ_eq_prod_range (fun i : ℕ => (X - C (ζ ^ i * t) : Polynomial ℂ)) n).trans
      (X_pow_sub_C_eq_prod hζ hn rfl).symm
  rw [he, pow_add, map_neg]
  ring

/-- The actual root trace retains the unchanged roots as literal constants. -/
theorem collisionRootTuple_trace (j n : ℕ) (ζ t : ℂ) (H : ℂ → ℂ) :
    (∑ i : Fin (j + n), H (collisionRootTuple j n ζ t i)) =
      (j : ℂ) * H 0 + ∑ i : Fin n, H (ζ ^ i.val * t) := by
  rw [Fin.sum_univ_add]
  simp only [collisionRootTuple, Fin.append_left, Fin.append_right, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Each lower coefficient of this exact product is the specified single coordinate. -/
theorem collisionRootTuple_coefficient (j : ℕ) {n : ℕ} (hn : 0 < n)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (t : ℂ) (i : Fin (j + n)) :
    (∏ a : Fin (j + n), (X - C (collisionRootTuple j n ζ t a))).coeff i.val =
      if i.val = j then -(t ^ n) else 0 := by
  rw [collisionRootTuple_polynomial j hn hζ t, coeff_add, coeff_X_pow,
    if_neg (Nat.ne_of_lt i.isLt), zero_add, coeff_C_mul_X_pow]

#print axioms collisionRootTuple_polynomial
#print axioms collisionRootTuple_trace
#print axioms collisionRootTuple_coefficient
end HodgeLean.Foundations.Program.G32Native
