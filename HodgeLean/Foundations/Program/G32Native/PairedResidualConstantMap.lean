import HodgeLean.Foundations.Program.TorusAlgebraizationB55Graph

/-! # Actual constant scheme morphisms and their complex points -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The constant map through the specified complex point retains the original base morphism. -/
def residualConstantMap (X Y : Over (Spec ↧ℂ)) (y : ComplexPoint Y) : X ⟶ Y :=
  Over.homMk (X.hom ≫ y.left) (by
    rw [Category.assoc, Over.w y]
    change X.hom ≫ 𝟙 _ = X.hom
    exact Category.comp_id _)

#print axioms residualConstantMap
/-- Every complex point maps to the specified point under the actual constant morphism. -/
theorem residualConstantMap_point (X Y : Over (Spec ↧ℂ)) (y : ComplexPoint Y)
    (x : ComplexPoint X) : Point.map (residualConstantMap X Y y) x = y := by
  apply Over.OverMorphism.ext
  change x.left ≫ (X.hom ≫ y.left) = y.left
  rw [← Category.assoc, Over.w x]
  change 𝟙 _ ≫ y.left = y.left
  exact Category.id_comp _

#print axioms residualConstantMap_point
/-- On a reduced finite-type source, a constant complex-point equation determines the scheme map. -/
theorem residual_eq_constantMap
    (X Y : Over (Spec ↧ℂ)) [IsReduced X.left] [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (y : ComplexPoint Y) (hf : ∀ x : ComplexPoint X, Point.map f x = y) :
    f = residualConstantMap X Y y := by
  apply b55_hom_ext
  funext x
  exact (hf x).trans (residualConstantMap_point X Y y x).symm

#print axioms residual_eq_constantMap
end HodgeLean.Foundations.Program.G32Native
