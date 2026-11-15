import HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData
import HodgeLean.Adapters.AbelianCMData

noncomputable section
open scoped Quaternion CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open Module
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- Transposing the actual opposite-valued cohomology action gives a left
quaternion action on rational homology. -/
def typeIIIHomologyAction (b : ℚ) (θ : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] AbelianEnd0 A) :
    ℍ[ℚ, -3, 0, b] →ₐ[ℚ] Module.End ℚ (Dual ℚ (HQ A 1)) where
  toFun q := ((abelianEnd0Action A (θ q)).unop).dualMap
  map_one' := by ext φ v; simp
  map_mul' q r := by ext φ v; simp [Module.End.mul_apply]
  map_zero' := by ext φ v; simp
  map_add' q r := by ext φ v; simp
  commutes' r := by
    ext φ v
    simp [Algebra.algebraMap_eq_smul_one]

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIHomologyAction
