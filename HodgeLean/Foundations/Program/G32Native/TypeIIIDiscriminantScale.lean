import HodgeLean.Foundations.HermitianForm
import HodgeLean.Foundations.Program.G32Native.TypeIIIThreeBlockDeterminant

noncomputable section
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.HermitianForm

/-- The factors from `H = 2u conjugate(T_K)` and from three quaternionic
blocks reduce to `−b disc(T)` in the norm quotient. The removed factor is
`1728 b² = Nm(24 b u)`.
Source: G32 v0.16, Lemma 8.1, final equations in its proof. -/
theorem typeIII_discriminant_scale_class (b d : ℚˣ) :
    ((Units.mk0 (-1728 : ℚ) (by norm_num) * b ^ 3 * d : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) =
      ((-b * d : ℚˣ) : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
  let n : ℚˣ := Units.mk0 (1728 : ℚ) (by norm_num) * b ^ 2
  apply mk_eq_mk_of_eq_mul (n := n)
  · apply mem_normSubgroup_iff.mpr
    refine ⟨⟨0, 24 * (b : ℚ)⟩, ?_⟩
    simp only [QuadraticAlgebra.norm_def, n, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_mk0]
    ring
  · simp only [n, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_neg]
    ring

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_discriminant_scale_class
