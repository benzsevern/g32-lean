import HodgeLean.Foundations.Program.G32Native.TypeIIITraceEntries

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Program.G32Native

/-- Rational coordinates for the quaternion basis `(1,j)` over the
Eisenstein quadratic algebra. -/
def typeIIIQuaternionCoordinates (b : ℚ) :
    ℍ[ℚ, -3, 0, b] ≃ₗ[ℚ] (Fin 2 → QuadraticAlgebra ℚ (-3) 0) where
  toFun q := ![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩]
  invFun x := ⟨(x 0).re, (x 0).im, (x 1).re, (x 1).im⟩
  left_inv q := by cases q; rfl
  right_inv x := by ext i <;> fin_cases i <;> rfl
  map_add' x y := by ext i <;> fin_cases i <;> rfl
  map_smul' c x := by ext i <;> fin_cases i <;> rfl

/-- Left multiplication by `u` acts as the quadratic generator in both
coordinates; the two indices refer to `(1,j)` in this order. -/
theorem typeIIIQuaternionCoordinates_generator (b : ℚ) (q : ℍ[ℚ, -3, 0, b])
    (i : Fin 2) :
    typeIIIQuaternionCoordinates b ((⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, b]) * q) i =
      (⟨0, 1⟩ : QuadraticAlgebra ℚ (-3) 0) * typeIIIQuaternionCoordinates b q i := by
  fin_cases i <;> ext <;>
    simp [typeIIIQuaternionCoordinates, QuaternionAlgebra.mk_mul_mk,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternionCoordinates
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternionCoordinates_generator
