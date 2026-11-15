import HodgeLean.Foundations.Program.G32Native.BlowupNormalizedCoordinates
import HodgeLean.Ported.Hironaka.Scheme.BlowUp.Composite.Descend

/-! Exceptional-generator multiplication as pullback of a base section. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData
namespace HodgeLean.Foundations.Program

/-- The product of a normalized coordinate and the exceptional generator is the base pullback. -/
theorem g32l4_blowUp_chart_coordinate_product {X : Scheme.{0}} (I : X.IdealSheafData)
    (U : X.affineOpens) (a b : I.ideal U) :
    affineBlowUp.chartGenerator (I.ideal U) a * g32l4_blowUp_coordinate (I.ideal U) a b =
      (blowUp.chart I U a ≫ I.blowUpπ).appLE U.1 ⊤ (chart_comp_le I U a) (b : Γ(X, U)) := by
  rw [g32l4_blowUp_coordinate_mul, appLE_chart_comp_π]

end HodgeLean.Foundations.Program
