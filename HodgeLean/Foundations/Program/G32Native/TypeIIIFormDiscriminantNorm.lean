import HodgeLean.Foundations.Program.G32Native.TypeIIIFormDiscriminant

noncomputable section
open scoped Quaternion CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite

/-- The ratio of discriminant representatives in two diagonal presentations
is a field norm. This retains the units before taking the quotient. -/
theorem TypeIIISixfoldData.discriminant_ratio_mem_norm (Q R : TypeIIISixfoldData A pol)
    (hJ : Q.inducedWeilAction.J = R.inducedWeilAction.J) :
    Q.discriminantUnit / R.discriminantUnit ∈
      normSubgroup (QuadraticAlgebra ℚ (-3) 0) := by
  apply (QuotientGroup.eq_one_iff _).mp
  rw [QuotientGroup.mk_div, Q.discriminant_class_eq R hJ, div_self']

/-- With the quaternion parameter fixed, the ratio of products of the three
pure quaternion squares is a norm. The common factor −b cancels. -/
theorem TypeIIISixfoldData.diagonal_product_ratio_mem_norm
    (Q R : TypeIIISixfoldData A pol) (hb : Q.b = R.b)
    (hJ : Q.inducedWeilAction.J = R.inducedWeilAction.J) :
    (∏ i, Units.mk0 (-3 * Q.l1 i ^ 2 + Q.b * Q.l2 i ^ 2 +
        3 * Q.b * Q.l3 i ^ 2) (Q.diagonal_nonzero i)) /
      (∏ i, Units.mk0 (-3 * R.l1 i ^ 2 + R.b * R.l2 i ^ 2 +
        3 * R.b * R.l3 i ^ 2) (R.diagonal_nonzero i)) ∈
      normSubgroup (QuadraticAlgebra ℚ (-3) 0) := by
  have h := Q.discriminant_ratio_mem_norm R hJ
  unfold TypeIIISixfoldData.discriminantUnit at h
  have hu : Units.mk0 Q.b (ne_of_lt Q.b_neg) = Units.mk0 R.b (ne_of_lt R.b_neg) :=
    Units.ext hb
  rw [hu, mul_div_mul_left_eq_div] at h
  exact h

end HodgeLean.Foundations.Program.G32Native
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.discriminant_ratio_mem_norm
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.diagonal_product_ratio_mem_norm
