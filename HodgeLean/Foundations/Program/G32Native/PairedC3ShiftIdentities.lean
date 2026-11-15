import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.ProjSpaceCechShiftedFractions

/-! # Integer shifts of the actual graded module -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native
open ProjSpaceCech

/-- Consecutive grading shifts add without changing the underlying module. -/
theorem paired_c3_shift_add {R : Type*} [CommRing R] {n : ℕ}
    (D : GradedModule R n) (a b : ℤ) :
    (D.shift a).shift b = D.shift (a + b) := by
  cases D
  simp only [GradedModule.shift]
  congr 1
  funext d
  congr 1
  omega

#print axioms paired_c3_shift_add
/-- Zero shift is the same graded module, with the original carrier and operators. -/
theorem paired_c3_shift_zero {R : Type*} [CommRing R] {n : ℕ}
    (D : GradedModule R n) : D.shift 0 = D := by
  cases D
  simp only [GradedModule.shift, add_zero]

#print axioms paired_c3_shift_zero
end HodgeLean.Foundations.Program.G32Native
