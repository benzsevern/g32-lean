import HodgeLean.Foundations.Program.G32Native.BlowupNormalizedCoordinates

/-! Normalization of the denominator coordinate of a blow-up chart. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The coordinate corresponding to the chart denominator equals one, including empty charts. -/
theorem g32l4_blowUp_coordinate_self {R : Type} [CommRing R] (I : Ideal R) (a : I) :
    g32l4_blowUp_coordinate I a a = 1 := by
  apply (mul_cancel_left_mem_nonZeroDivisors
    (affineBlowUp.chartGenerator_mem_nonZeroDivisors I a)).mp
  rw [g32l4_blowUp_coordinate_mul, mul_one]

end HodgeLean.Foundations.Program
