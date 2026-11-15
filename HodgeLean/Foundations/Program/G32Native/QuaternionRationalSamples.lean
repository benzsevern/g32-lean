import Mathlib.Algebra.Quaternion
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 200000
open scoped Quaternion
namespace HodgeLean.Foundations.Program.QuaternionGraph

/-- The rational one-parameter family used to sample the graph wedges. -/
def graphQuaternion (a b t : ℚ) : ℍ[ℚ,a,0,b] := ⟨1,0,t,0⟩

/-- Negativity of the second quaternion parameter keeps every sample denominator nonzero. -/
theorem graphQuaternion_denominator (b t : ℚ) (hb : b < 0) : 1 - b*t^2 ≠ 0 := by
  have h : b*t^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb.le (sq_nonneg t)
  linarith

/-- Every rational graph sample is an invertible quaternion. -/
def graphQuaternionUnit (a b t : ℚ) (hb : b < 0) : ℍ[ℚ,a,0,b]ˣ where
  val := graphQuaternion a b t
  inv := ⟨(1-b*t^2)⁻¹,0,-t*(1-b*t^2)⁻¹,0⟩
  val_inv := by
    ext <;> simp [graphQuaternion] <;>
      field_simp [graphQuaternion_denominator b t hb] <;> ring
  inv_val := by
    ext <;> simp [graphQuaternion] <;>
      field_simp [graphQuaternion_denominator b t hb] <;> ring

/-- The retained unit has the stated graph coordinates. -/
theorem graphQuaternionUnit_val (a b t : ℚ) (hb : b < 0) :
    (graphQuaternionUnit a b t hb : ℍ[ℚ,a,0,b]) = ⟨1,0,t,0⟩ := rfl

#print axioms graphQuaternionUnit
end HodgeLean.Foundations.Program.QuaternionGraph
