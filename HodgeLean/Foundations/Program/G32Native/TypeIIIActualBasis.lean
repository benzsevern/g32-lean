import HodgeLean.Foundations.Program.G32Native.TypeIIIConjugateCoordinates

noncomputable section
open scoped Quaternion CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.WeilHermitian
open Module
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite

/-- Quadratic coordinates for the actual cohomology operator. -/
def TypeIIISixfoldData.cohomologyQuadraticCoordinates (Q : TypeIIISixfoldData A pol) :
    WithJ (HQ A 1) ⟨Q.inducedWeilAction.J, Q.inducedWeilAction.J_sq⟩ ≃ₗ[
      QuadraticAlgebra ℚ (-3) 0] (Fin 2 × Fin 3 → QuadraticAlgebra ℚ (-3) 0) :=
  typeIIIQuadraticCoordinates _ Q.cohomologyRationalCoordinates
    Q.cohomologyRationalCoordinates_generator

/-- The six quadratic basis vectors on actual cohomology. -/
def TypeIIISixfoldData.cohomologyBasis (Q : TypeIIISixfoldData A pol) :
    Basis (Fin 2 × Fin 3) (QuadraticAlgebra ℚ (-3) 0)
      (WithJ (HQ A 1) ⟨Q.inducedWeilAction.J, Q.inducedWeilAction.J_sq⟩) :=
  (Pi.basisFun _ _).map Q.cohomologyQuadraticCoordinates.symm

/-- The associated homology vectors before contraction. -/
def TypeIIISixfoldData.homologyBasisVector (Q : TypeIIISixfoldData A pol)
    (p : Fin 2 × Fin 3) : Dual ℚ (HQ A 1) :=
  Q.homologyCoordinates.symm (Pi.single p 1)

/-- Contraction takes the retained homology vectors to the cohomology basis. -/
theorem TypeIIISixfoldData.cohomologyBasis_apply (Q : TypeIIISixfoldData A pol)
    (p : Fin 2 × Fin 3) :
    WithJ.equiv ⟨Q.inducedWeilAction.J, Q.inducedWeilAction.J_sq⟩
      (Q.cohomologyBasis p) = contract (polarizationVec
        (torusCohomology_cupProductOf A) pol) (Q.homologyBasisVector p) := by
  change contractEquiv Q.nondegenerate (Q.homologyCoordinates.symm
    (fun i => star ((Pi.basisFun (QuadraticAlgebra ℚ (-3) 0) (Fin 2 × Fin 3)) p i))) = _
  change contract (polarizationVec (torusCohomology_cupProductOf A) pol)
    (Q.homologyCoordinates.symm _) = contract (polarizationVec
      (torusCohomology_cupProductOf A) pol) (Q.homologyCoordinates.symm _)
  apply congrArg (contract (polarizationVec (torusCohomology_cupProductOf A) pol))
  apply congrArg Q.homologyCoordinates.symm
  funext i
  by_cases hi : i = p <;> simp [Pi.basisFun_apply, Pi.single_apply, hi] <;> rfl

/-- The homology vector has just one quaternionic component, with value `1`
or `j` according to its first index. -/
theorem TypeIIISixfoldData.homologyBasisVector_apply (Q : TypeIIISixfoldData A pol)
    (p : Fin 2 × Fin 3) (i : Fin 3) :
    Q.homology (Q.homologyBasisVector p) i =
      if i = p.2 then typeIIIBlockVector Q.b p.1 else 0 := by
  rcases p with ⟨k, j⟩
  fin_cases k <;> by_cases hi : i = j <;>
    ext <;> simp [homologyBasisVector, homologyCoordinates, typeIIIQuaternionCoordinates,
      typeIIIBlockVector, Pi.single_apply, hi, eq_comm,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> rfl

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.cohomologyQuadraticCoordinates
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.cohomologyBasis
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.cohomologyBasis_apply
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.homologyBasisVector_apply
