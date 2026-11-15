import HodgeLean.Foundations.Program.SchoenCycleC1EtaleFibreHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1CoveringCardHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11Pre

/-! # Constant complex fibre size on the actual finite etale cover -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- All complex fibres of a finite etale surjection to a smooth integral
separated complex base have the same cardinality. -/
theorem s2e_c1_finite_etale_fibre_card_eq
    (X Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] [Surjective f.left]
    (x y : ComplexPoint Y) :
    Nat.card ((Point.map f) ⁻¹' {x}) = Nat.card ((Point.map f) ⁻¹' {y}) := by
  haveI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  haveI : ConnectedSpace (ComplexPoint Y) := AlgebraicGeometry.ComplexPoint.connectedSpace Y
  exact s2e_c1_covering_fibre_card_eq (Point.map f)
    (s2e_c1_finite_etale_analytic_cover X Y f).1
    (s2e_c11_finite_surjective_complex_points X Y f) x y

end HodgeLean.Foundations.Program
