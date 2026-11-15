import HodgeLean.Foundations.Program.G32Native.TypeIIIHermitianDeterminant
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.FinCases

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Program.G32Native

/-- The two quaternion vectors underlying the Eisenstein basis. -/
def typeIIIBlockVector (b : ℚ) (i : Fin 2) : ℍ[ℚ, -3, 0, b] :=
  if i = 0 then 1 else ⟨0, 0, 1, 0⟩

/-- The trace pairing in the basis `(1,j)` gives exactly the scaled conjugate
projected block, with the trace factor two retained. -/
theorem typeIII_trace_hermitian_entries (b l1 l2 l3 : ℚ) (i j : Fin 2) :
    let x := typeIIIBlockVector b i
    let y := typeIIIBlockVector b j
    let t : ℍ[ℚ, -3, 0, b] := ⟨0, l1, l2, l3⟩
    let u : ℍ[ℚ, -3, 0, b] := ⟨0, 1, 0, 0⟩
    (⟨2 * (x * t * star (u * y)).re, 2 * (x * t * star y).re⟩ :
        QuadraticAlgebra ℚ (-3) 0) =
      (⟨0, 2⟩ : QuadraticAlgebra ℚ (-3) 0) *
        star (typeIIIProjectedBlock b l1 l2 l3 i j) := by
  fin_cases i <;> fin_cases j <;>
    ext <;> simp [typeIIIBlockVector, typeIIIProjectedBlock,
      QuaternionAlgebra.mk_mul_mk, Star.star, QuaternionAlgebra.instStarQuaternionAlgebra,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_trace_hermitian_entries
