import HodgeLean.Foundations.Program.G32Native.TypeIIITraceFormSkew

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Program.G32Native
variable (b : ℚ) {V : Type*} [AddCommGroup V]
  [Module ℚ V] [Module ℍ[ℚ, -3, 0, b] V]
  [IsScalarTower ℚ ℍ[ℚ, -3, 0, b] V]

/-- Additivity of the recovered quaternion form in its first argument. -/
theorem typeIIIQuaternionTraceForm_add_left (B : LinearMap.BilinForm ℚ V) (x x' y : V) :
    typeIIIQuaternionTraceForm b B (x + x') y =
      typeIIIQuaternionTraceForm b B x y + typeIIIQuaternionTraceForm b B x' y := by
  ext <;> simp [typeIIIQuaternionTraceForm, smul_add, add_div, neg_add] <;> ring

/-- Additivity of the recovered quaternion form in its second argument. -/
theorem typeIIIQuaternionTraceForm_add_right (B : LinearMap.BilinForm ℚ V) (x y y' : V) :
    typeIIIQuaternionTraceForm b B x (y + y') =
      typeIIIQuaternionTraceForm b B x y + typeIIIQuaternionTraceForm b B x y' := by
  ext <;> simp [typeIIIQuaternionTraceForm, add_div, neg_add] <;> ring

/-- The diagonal values of an invariant alternating trace form are pure. -/
theorem typeIIIQuaternionTraceForm_diagonal_pure (hb : b ≠ 0)
    (B : LinearMap.BilinForm ℚ V) (hAlt : B.IsAlt)
    (hB : ∀ (q : ℍ[ℚ, -3, 0, b]) (x y : V), B (q • x) y = B x (star q • y))
    (x : V) : (typeIIIQuaternionTraceForm b B x x).re = 0 := by
  have h := congrArg QuaternionAlgebra.re
    (typeIIIQuaternionTraceForm_skew b hb B hAlt hB x x)
  simp only [QuaternionAlgebra.re_neg, QuaternionAlgebra.re_star, zero_mul, add_zero] at h
  linarith

/-- Nondegeneracy of the rational form gives nondegeneracy of the recovered
quaternion form in its first argument. -/
theorem typeIIIQuaternionTraceForm_nondegenerate (hb : b ≠ 0)
    (B : LinearMap.BilinForm ℚ V) (hnd : B.Nondegenerate) (x : V)
    (hx : ∀ y, typeIIIQuaternionTraceForm b B x y = 0) : x = 0 := by
  apply hnd.1 x
  intro y
  have h := typeIIIQuaternionTraceForm_trace b hb B x y 1
  rw [hx, mul_zero] at h
  simpa using h.symm

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternionTraceForm_add_left
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternionTraceForm_add_right
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternionTraceForm_diagonal_pure
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternionTraceForm_nondegenerate
