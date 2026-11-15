import HodgeLean.Foundations.Program.G32Native.TypeIIIActualTrace
import HodgeLean.Foundations.Program.G32Native.TypeIIIHermitianClass

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

/-- The Weil Hermitian form of the actual retained cohomology operator. -/
def TypeIIISixfoldData.cohomologyHermitian (Q : TypeIIISixfoldData A pol) :=
  weilHermitian (dualForm Q.nondegenerate)
    ⟨Q.inducedWeilAction.J, Q.inducedWeilAction.J_sq⟩
    ((isRosatiSkew_iff_dualForm Q.nondegenerate Q.inducedWeilAction.J).1 Q.generator_rosati)

/-- The actual cohomology Gram matrix is minus conjugation of the retained
homology trace matrix, with all six basis vectors and the trace scale. -/
theorem TypeIIISixfoldData.cohomologyHermitian_matrix (Q : TypeIIISixfoldData A pol) :
    LinearMap.toMatrix₂ Q.cohomologyBasis Q.cohomologyBasis Q.cohomologyHermitian =
      -(typeIIIHermitianMatrix Q.b Q.l1 Q.l2 Q.l3).map (starRingEnd _) := by
  apply Matrix.ext
  intro p q
  simp only [LinearMap.toMatrix₂_apply]
  change (⟨dualForm Q.nondegenerate
    (WithJ.equiv _ (Q.cohomologyBasis p))
    (Q.inducedWeilAction.J (WithJ.equiv _ (Q.cohomologyBasis q))),
    dualForm Q.nondegenerate (WithJ.equiv _ (Q.cohomologyBasis p))
      (WithJ.equiv _ (Q.cohomologyBasis q))⟩ : QuadraticAlgebra ℚ (-3) 0) = _
  rw [Q.cohomologyBasis_apply, Q.cohomologyBasis_apply,
    typeIII_dual_hermitian_expression Q.nondegenerate Q.inducedWeilAction.J
      Q.generator_rosati (Q.homologyBasisVector p) (Q.homologyBasisVector q),
    Q.trace_basis_generator, Q.trace_basis]
  change _ = -star (typeIIIHermitianMatrix Q.b Q.l1 Q.l2 Q.l3 p q)
  by_cases hpq : p.2 = q.2
  · simp only [hpq, ite_true]
    rw [typeIII_trace_hermitian_entries]
    simp only [typeIIIHermitianMatrix, Matrix.smul_apply, Matrix.map_apply,
      Matrix.blockDiagonal_apply, hpq, ite_true, starRingEnd_apply, smul_eq_mul]
  · simp [typeIIIHermitianMatrix, Matrix.blockDiagonal_apply, hpq]

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.cohomologyHermitian_matrix
