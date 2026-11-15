import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Cotangent

/-! # Coordinate functionals on the affine conormal module -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Partial differentiation modulo an ideal is linear on that ideal. -/
def s2e_idealDerivative {R σ : Type*} [CommRing R]
    (I : Ideal (MvPolynomial σ R)) (i : σ) :
    I →ₗ[MvPolynomial σ R] MvPolynomial σ R ⧸ I where
  toFun f := Ideal.Quotient.mk I (pderiv i f.val)
  map_add' f g := by simp only [Submodule.coe_add, map_add]
  map_smul' a f := by
    change Ideal.Quotient.mk I (pderiv i (a * f.val)) = _
    rw [pderiv_mul, map_add, map_mul, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.mpr f.property, mul_zero, zero_add]
    rfl

/-- The derivative functional vanishes on products of two elements of the ideal. -/
theorem s2e_idealDerivative_mul {R σ : Type*} [CommRing R]
    (I : Ideal (MvPolynomial σ R)) (i : σ) (f g : I) :
    s2e_idealDerivative I i (f * g) = 0 := by
  change Ideal.Quotient.mk I (pderiv i (f.val * g.val)) = 0
  rw [pderiv_mul, map_add, map_mul, map_mul,
    Ideal.Quotient.eq_zero_iff_mem.mpr f.property,
    Ideal.Quotient.eq_zero_iff_mem.mpr g.property, zero_mul, mul_zero, add_zero]

/-- The partial derivative modulo the ideal descends to the actual affine module I/I². -/
def s2e_cotangentCoordinate {R σ : Type*} [CommRing R]
    (I : Ideal (MvPolynomial σ R)) (i : σ) :
    I.Cotangent →ₗ[MvPolynomial σ R] MvPolynomial σ R ⧸ I :=
  Ideal.Cotangent.lift (s2e_idealDerivative I i) (s2e_idealDerivative_mul I i)

/-- A coordinate class is detected by its corresponding derivative functional. -/
theorem s2e_cotangentCoordinate_variable {R σ : Type*} [CommRing R] [DecidableEq σ]
    (I : Ideal (MvPolynomial σ R)) (i j : σ) (hj : X j ∈ I) :
    s2e_cotangentCoordinate I i (I.toCotangent ⟨X j, hj⟩) =
      if j = i then 1 else 0 := by
  change Ideal.Quotient.mk I (pderiv i (X j)) = _
  rw [pderiv_X]
  split_ifs with h
  · subst j; simp
  · simp [Pi.single_apply, h]

end HodgeLean.Foundations.Program
