import HodgeLean.Foundations.Program.G32Native.TypeIIIActualMatrix

noncomputable section
open scoped Quaternion CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.WeilHermitian
open HodgeLean.Foundations.HermitianForm
open Module
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite

/-- The rational Gram determinant in the actual cohomology basis. -/
theorem TypeIIISixfoldData.cohomologyGramDet (Q : TypeIIISixfoldData A pol) :
    gramDetℚ Q.cohomologyHermitian Q.cohomologyBasis =
      -1728 * Q.b ^ 3 * ∏ i, (-3 * Q.l1 i ^ 2 + Q.b * Q.l2 i ^ 2 +
        3 * Q.b * Q.l3 i ^ 2) := by
  unfold gramDetℚ gramDet
  rw [Q.cohomologyHermitian_matrix,
    typeIII_det_neg_conjugate _ _ (typeIIIHermitianMatrix_det Q.b Q.l1 Q.l2 Q.l3)
      (by norm_num [Fintype.card_prod])]
  rfl

/-- The retained operator has exactly the manuscript's norm class on actual
cohomology, with dual transport included. -/
theorem TypeIIISixfoldData.discriminant_class (Q : TypeIIISixfoldData A pol) :
    weilDatumClass (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      Q.inducedWeilAction Q.nondegenerate Q.generator_rosati =
        (Q.discriminantUnit : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
  have hh : Q.cohomologyHermitian.IsSymm :=
    isSymm_weilHermitian (isAlt_dualForm Q.nondegenerate)
  have hn : Q.cohomologyHermitian.Nondegenerate :=
    nondegenerate_weilHermitian (nondegenerate_dualForm Q.nondegenerate)
  change detClass Q.cohomologyHermitian hh hn = _
  rw [detClass_eq hh hn Q.cohomologyBasis]
  let b : ℚˣ := Units.mk0 Q.b (ne_of_lt Q.b_neg)
  let d : ℚˣ := ∏ i, Units.mk0
    (-3 * Q.l1 i ^ 2 + Q.b * Q.l2 i ^ 2 + 3 * Q.b * Q.l3 i ^ 2)
    (Q.diagonal_nonzero i)
  calc
    _ = ((Units.mk0 (-1728 : ℚ) (by norm_num) * b ^ 3 * d : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
      apply congrArg (fun u : ℚˣ =>
        (u : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)))
      ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
        b, d, Units.coe_prod, Q.cohomologyGramDet]
    _ = _ := typeIII_discriminant_scale_class b d

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.cohomologyGramDet
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.discriminant_class
