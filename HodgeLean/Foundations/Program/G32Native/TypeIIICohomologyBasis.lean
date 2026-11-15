import HodgeLean.Foundations.Program.G32Native.TypeIIIInducedAction
import HodgeLean.Foundations.Program.G32Native.TypeIIIQuaternionCoordinates
import HodgeLean.Foundations.Program.G32Native.TypeIIIQuadraticCoordinates
import HodgeLean.Foundations.Program.G32Native.TypeIIIDualTransport

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

/-- The retained homology presentation in six rational quadratic coordinates. -/
def TypeIIISixfoldData.homologyCoordinates (Q : TypeIIISixfoldData A pol) :
    Dual ℚ (HQ A 1) ≃ₗ[ℚ] (Fin 2 × Fin 3 → QuadraticAlgebra ℚ (-3) 0) where
  toFun x p := typeIIIQuaternionCoordinates Q.b (Q.homology x p.2) p.1
  invFun x := Q.homology.symm (fun i => (typeIIIQuaternionCoordinates Q.b).symm
    (fun k => x (k, i)))
  left_inv x := by
    apply Q.homology.injective
    simp only [LinearEquiv.apply_symm_apply]
    funext i
    exact (typeIIIQuaternionCoordinates Q.b).symm_apply_apply _
  right_inv x := by
    funext p
    simp only [LinearEquiv.apply_symm_apply]
  map_add' x y := by funext p; simp
  map_smul' c x := by funext p; simp

/-- The dual of the retained cohomology operator acts as the quadratic
 generator on all six homology coordinates. -/
theorem TypeIIISixfoldData.homologyCoordinates_generator (Q : TypeIIISixfoldData A pol)
    (x : Dual ℚ (HQ A 1)) (p : Fin 2 × Fin 3) :
    Q.homologyCoordinates (Q.inducedWeilAction.J.dualMap x) p =
      (⟨0, 1⟩ : QuadraticAlgebra ℚ (-3) 0) * Q.homologyCoordinates x p := by
  change typeIIIQuaternionCoordinates Q.b
    (Q.homology (((Q.pullback (Q.endomorphisms
      (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, Q.b]))).unop).dualMap x) p.2) p.1 = _
  rw [Q.homology_action]
  exact typeIIIQuaternionCoordinates_generator _ _ _

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.homologyCoordinates
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.homologyCoordinates_generator
