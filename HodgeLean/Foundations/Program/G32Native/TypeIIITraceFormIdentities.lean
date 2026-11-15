import HodgeLean.Foundations.Program.G32Native.TypeIIIQuaternionTraceForm

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Program.G32Native

/-- Pairing by reduced trace against every quaternion determines a quaternion. -/
theorem typeIIIQuaternion_trace_ext (b : ℚ) (hb : b ≠ 0)
    (x y : ℍ[ℚ, -3, 0, b])
    (h : ∀ a, 2 * (a * x).re = 2 * (a * y).re) : x = y := by
  have hr := h 1
  have hi := h ⟨0, 1, 0, 0⟩
  have hj := h ⟨0, 0, 1, 0⟩
  have hk := h ⟨0, 0, 0, 1⟩
  simp [QuaternionAlgebra.re_mul] at hr hi hj hk
  ext
  · exact hr
  · exact hi
  · exact hj.resolve_right hb
  · exact hk.resolve_right hb

/-- The recovered trace form is quaternion linear in the first argument. -/
theorem typeIIIQuaternionTraceForm_smul_left (b : ℚ) (hb : b ≠ 0)
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℍ[ℚ, -3, 0, b] V]
    [IsScalarTower ℚ ℍ[ℚ, -3, 0, b] V]
    (B : LinearMap.BilinForm ℚ V) (x y : V) (q : ℍ[ℚ, -3, 0, b]) :
    typeIIIQuaternionTraceForm b B (q • x) y = q * typeIIIQuaternionTraceForm b B x y := by
  apply typeIIIQuaternion_trace_ext b hb
  intro a
  rw [typeIIIQuaternionTraceForm_trace b hb, ← mul_assoc,
    typeIIIQuaternionTraceForm_trace b hb, mul_smul]

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternion_trace_ext
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternionTraceForm_smul_left
