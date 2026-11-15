import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5AvoidanceProofs
import HodgeLean.Foundations.Curves.CubicS13
import HodgeLean.Adapters.AbelianPowerLink

/-! # Explicit forms for the stage-six witness split

These are functions and forms, with no geometric existence predicates.
The Hermitian convention is conjugate-linear in the first argument.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
namespace HodgeLean.Adapters

/-- The normalized elliptic Hermitian form, in the repository's convention.
Source: Birkenhake--Lange, second edition, sections 1.3 and 2.2. -/
def bh6_ellipticForm (τ : ℂ) : HermitianForm (V := ℂ) where
  toFun z w := star z * w / (τ.im : ℂ)
  add_left x y z := by simp [add_mul, add_div]
  smul_left c x y := by simp [mul_assoc, mul_div_assoc]
  add_right x y z := by simp [mul_add, add_div]
  smul_right c x y := by simp [mul_div_assoc]; ring
  conj_symm x y := by simp [mul_comm]

example : (bh6_ellipticForm Complex.I).toFun 1 1 = 1 := by
  simp [bh6_ellipticForm]

/-- Pull a Hermitian form back along a complex linear map.
Source: Birkenhake--Lange, second edition, section 1.3, pullback of forms. -/
def bh6_pullForm (n : ℕ) (q : (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (H : HermitianForm (V := ℂ)) : HermitianForm (V := Fin n → ℂ) where
  toFun v w := H.toFun (q v) (q w)
  add_left x y z := by rw [map_add, H.add_left]
  smul_left c x y := by rw [map_smul, H.smul_left]
  add_right x y z := by rw [map_add, H.add_right]
  smul_right c x y := by rw [map_smul, H.smul_right]
  conj_symm x y := H.conj_symm _ _

example (n : ℕ) : (bh6_pullForm n 0 (bh6_ellipticForm Complex.I)).toFun 0 0 = 0 := by
  simp [bh6_pullForm, bh6_ellipticForm]

/-- The sum of the two factor forms, pulled back by a linear map of covering spaces.
Source: Birkenhake--Lange, second edition, section 4.3, product polarizations. -/
def bh6_productForm (n m : ℕ)
    (q : (Fin m → ℂ) →ₗ[ℂ] (Fin 2 → (Fin n → ℂ)))
    (H : HermitianForm (V := Fin n → ℂ)) : HermitianForm (V := Fin m → ℂ) where
  toFun v w := H.toFun (q v 0) (q w 0) + H.toFun (q v 1) (q w 1)
  add_left x y z := by simp only [map_add, Pi.add_apply, H.add_left]; ring
  smul_left c x y := by simp only [map_smul, Pi.smul_apply, H.smul_left]; ring
  add_right x y z := by simp only [map_add, Pi.add_apply, H.add_right]; ring
  smul_right c x y := by simp only [map_smul, Pi.smul_apply, H.smul_right]; ring
  conj_symm x y := by rw [star_add, H.conj_symm, H.conj_symm]

example (n m : ℕ) (q : (Fin m → ℂ) →ₗ[ℂ] (Fin 2 → (Fin n → ℂ))) :
    (bh6_productForm n m q HermitianForm.zero).toFun 0 0 = 0 := by
  simp [bh6_productForm, HermitianForm.zero]

end HodgeLean.Adapters
