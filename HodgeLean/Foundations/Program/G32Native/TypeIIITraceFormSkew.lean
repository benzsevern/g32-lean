import HodgeLean.Foundations.Program.G32Native.TypeIIITraceFormIdentities
import Mathlib.LinearAlgebra.BilinearForm.Properties

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Program.G32Native

/-- The rational trace of a quaternion product is cyclic. -/
theorem typeIIIQuaternion_re_mul_comm (b : ℚ) (x y : ℍ[ℚ, -3, 0, b]) :
    (x * y).re = (y * x).re := by
  simp only [QuaternionAlgebra.re_mul]
  ring

/-- The recovered invariant trace form is conjugate linear in the second
argument, with multiplication on the right. -/
theorem typeIIIQuaternionTraceForm_smul_right (b : ℚ) (hb : b ≠ 0)
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℍ[ℚ, -3, 0, b] V]
    [IsScalarTower ℚ ℍ[ℚ, -3, 0, b] V]
    (B : LinearMap.BilinForm ℚ V)
    (hB : ∀ (q : ℍ[ℚ, -3, 0, b]) (x y : V), B (q • x) y = B x (star q • y))
    (x y : V) (q : ℍ[ℚ, -3, 0, b]) :
    typeIIIQuaternionTraceForm b B x (q • y) =
      typeIIIQuaternionTraceForm b B x y * star q := by
  apply typeIIIQuaternion_trace_ext b hb
  intro a
  rw [typeIIIQuaternionTraceForm_trace b hb]
  calc
    B (a • x) (q • y) = B (star q • (a • x)) y := by
      simpa only [star_star] using (hB (star q) (a • x) y).symm
    _ = B ((star q * a) • x) y := by rw [mul_smul]
    _ = 2 * ((star q * a) * typeIIIQuaternionTraceForm b B x y).re :=
      (typeIIIQuaternionTraceForm_trace b hb B x y _).symm
    _ = _ := by
      rw [mul_assoc, typeIIIQuaternion_re_mul_comm b (star q), mul_assoc]

/-- For an alternating invariant rational pairing, the recovered quaternion
form is skew-Hermitian. -/
theorem typeIIIQuaternionTraceForm_skew (b : ℚ) (hb : b ≠ 0)
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℍ[ℚ, -3, 0, b] V]
    [IsScalarTower ℚ ℍ[ℚ, -3, 0, b] V]
    (B : LinearMap.BilinForm ℚ V) (hAlt : B.IsAlt)
    (hB : ∀ (q : ℍ[ℚ, -3, 0, b]) (x y : V), B (q • x) y = B x (star q • y)) (x y : V) :
    typeIIIQuaternionTraceForm b B y x = -star (typeIIIQuaternionTraceForm b B x y) := by
  apply typeIIIQuaternion_trace_ext b hb
  intro a
  rw [typeIIIQuaternionTraceForm_trace b hb]
  calc
    B (a • y) x = -B x (a • y) := (LinearMap.IsAlt.neg hAlt x (a • y)).symm
    _ = -B (star a • x) y := by
      rw [hB (star a), star_star]
    _ = -(2 * (star a * typeIIIQuaternionTraceForm b B x y).re) := by
      rw [typeIIIQuaternionTraceForm_trace b hb]
    _ = _ := by
      have ht : (star a * typeIIIQuaternionTraceForm b B x y).re =
          (a * star (typeIIIQuaternionTraceForm b B x y)).re := by
        rw [typeIIIQuaternion_re_mul_comm b (star a)]
        have hs := congrArg QuaternionAlgebra.re
          (star_mul (typeIIIQuaternionTraceForm b B x y) (star a))
        simpa only [QuaternionAlgebra.re_star, zero_mul, add_zero, star_star] using hs
      rw [ht, mul_neg, QuaternionAlgebra.re_neg]
      ring

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternion_re_mul_comm
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternionTraceForm_smul_right
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternionTraceForm_skew
