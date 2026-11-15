import HodgeLean.Foundations.Program.G32Native.TypeIIIDefiniteQuaternion
import Mathlib.Tactic.FieldSimp

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Program.G32Native

/-- The quaternion-valued form recovered from a rational pairing by its
four trace coefficients. -/
def typeIIIQuaternionTraceForm (b : ℚ) {V : Type*} [AddCommGroup V]
    [Module ℚ V] [Module ℍ[ℚ, -3, 0, b] V]
    (B : LinearMap.BilinForm ℚ V) (x y : V) : ℍ[ℚ, -3, 0, b] :=
  ⟨B x y / 2,
    -B ((⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, b]) • x) y / 6,
    B ((⟨0, 0, 1, 0⟩ : ℍ[ℚ, -3, 0, b]) • x) y / (2 * b),
    B ((⟨0, 0, 0, 1⟩ : ℍ[ℚ, -3, 0, b]) • x) y / (6 * b)⟩

/-- The reconstructed form represents the rational pairing against every
quaternion, with the reduced-trace factor two retained. -/
theorem typeIIIQuaternionTraceForm_trace (b : ℚ) (hb : b ≠ 0)
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℍ[ℚ, -3, 0, b] V]
    [IsScalarTower ℚ ℍ[ℚ, -3, 0, b] V]
    (B : LinearMap.BilinForm ℚ V) (x y : V) (a : ℍ[ℚ, -3, 0, b]) :
    2 * (a * typeIIIQuaternionTraceForm b B x y).re = B (a • x) y := by
  have ha : a = a.re • (1 : ℍ[ℚ, -3, 0, b]) +
      a.imI • (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, b]) +
      a.imJ • (⟨0, 0, 1, 0⟩ : ℍ[ℚ, -3, 0, b]) +
      a.imK • (⟨0, 0, 0, 1⟩ : ℍ[ℚ, -3, 0, b]) := by
    ext <;> simp
  calc
    _ = a.re * B x y + a.imI * B ((⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, b]) • x) y +
        a.imJ * B ((⟨0, 0, 1, 0⟩ : ℍ[ℚ, -3, 0, b]) • x) y +
        a.imK * B ((⟨0, 0, 0, 1⟩ : ℍ[ℚ, -3, 0, b]) • x) y := by
      simp only [typeIIIQuaternionTraceForm, QuaternionAlgebra.re_mul]
      field_simp [hb]
      <;> ring
    _ = _ := by
      conv_rhs => rw [ha]
      simp only [add_smul, smul_assoc, one_smul, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternionTraceForm_trace
