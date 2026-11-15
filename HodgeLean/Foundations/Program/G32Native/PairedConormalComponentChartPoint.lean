import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialChartPoint
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalComponentPoint

/-! # The actual component point and its normalized polynomial chart arrow -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The component point and the normalized polynomial point have literally
identical arrows into the specified original projective space. -/
theorem conormal_component_chart_point {Q : Over (Spec ↧ℂ)} (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (w : ℂ × (Fin k → ℂ)) (hw : w ≠ 0) (i : Fin (k + 1))
    (hi : EulerModel.normalHomogeneousCoordinates k w i ≠ 0) :
    (EulerModel.normalComponentHomeomorph k eQ (Projectivization.mk ℂ w hw)).left ≫
        eQ.hom.left =
      (conormalPolynomialChartComplexPoint (EulerModel.normalHomogeneousCoordinates k w)
        i hi).left ≫ (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom := by
  have he : Point.map eQ.hom
      (EulerModel.normalComponentHomeomorph k eQ (Projectivization.mk ℂ w hw)) =
      EulerModel.normalProjectiveSchemeHomeomorph k (Projectivization.mk ℂ w hw) :=
    (Point.isoMapHomeomorph eQ.symm).symm_apply_apply _
  have hh := congrArg (fun x => x.left) he
  rw [EulerModel.normalProjectiveSchemeHomeomorph_mk] at hh
  exact hh.trans (conormal_polynomial_chart_point_original
    (EulerModel.normalHomogeneousCoordinates k w) i hi).symm

#print axioms conormal_component_chart_point
end HodgeLean.Foundations.Program.G32Native
