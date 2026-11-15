import HodgeLean.Foundations.Program.G32Native.TypeIIICohomologyBasis
import HodgeLean.Foundations.Program.G32Native.TypeIIIRosati

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

/-- Conjugation of each quadratic coordinate as a rational equivalence. -/
def typeIIIConjugateCoordinates {Index : Type*} :
    (Index → QuadraticAlgebra ℚ (-3) 0) ≃ₗ[ℚ] (Index → QuadraticAlgebra ℚ (-3) 0) where
  toFun x i := star (x i)
  invFun x i := star (x i)
  left_inv x := by funext i; exact star_star _
  right_inv x := by funext i; exact star_star _
  map_add' x y := by funext i; exact star_add _ _
  map_smul' c x := by funext i; simp

/-- Coordinates on cohomology obtained by inverse contraction followed by
conjugation of the retained homology coordinates. -/
def TypeIIISixfoldData.cohomologyRationalCoordinates (Q : TypeIIISixfoldData A pol) :
    HQ A 1 ≃ₗ[ℚ] (Fin 2 × Fin 3 → QuadraticAlgebra ℚ (-3) 0) :=
  ((contractEquiv Q.nondegenerate).symm.trans Q.homologyCoordinates).trans
    typeIIIConjugateCoordinates

/-- Conjugation compensates for the generator reversal of contraction. -/
theorem TypeIIISixfoldData.cohomologyRationalCoordinates_generator
    (Q : TypeIIISixfoldData A pol) (x : HQ A 1) (p : Fin 2 × Fin 3) :
    Q.cohomologyRationalCoordinates (Q.inducedWeilAction.J x) p =
      (⟨0, 1⟩ : QuadraticAlgebra ℚ (-3) 0) * Q.cohomologyRationalCoordinates x p := by
  change star (Q.homologyCoordinates ((contractEquiv Q.nondegenerate).symm
    (Q.inducedWeilAction.J x)) p) = _
  rw [typeIII_inverse_contract_anticommutes Q.nondegenerate
    Q.inducedWeilAction.J Q.generator_rosati, map_neg]
  change star (-(Q.homologyCoordinates
    (Q.inducedWeilAction.J.dualMap ((contractEquiv Q.nondegenerate).symm x)) p)) = _
  rw [Q.homologyCoordinates_generator, star_neg, star_mul]
  have hu : star (⟨0, 1⟩ : QuadraticAlgebra ℚ (-3) 0) = -⟨0, 1⟩ := by ext <;> simp
  rw [hu, mul_neg, neg_neg, mul_comm]
  rfl

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIConjugateCoordinates
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.cohomologyRationalCoordinates
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.cohomologyRationalCoordinates_generator
