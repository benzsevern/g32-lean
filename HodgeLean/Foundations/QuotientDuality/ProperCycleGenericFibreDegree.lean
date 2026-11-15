import HodgeLean.Foundations.QuotientDuality.ProperCycleGenericResidueDegree
import HodgeLean.Foundations.Program.SchoenCycleC1ActualFieldDegreeHelpers

/-! # Actual residue degrees measured by complex fibres on finite etale base charts -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual generic residue degree equals the cardinality of each complex fibre on an actual finite etale affine base chart.
Source: Fulton, Intersection Theory, section 1.4; SGA 1, Expose I, finite etale rank and geometric fibres.
HC no distance; AV milestone no distance. -/
lemma properCycle_generic_residue_degree_eq_etale_fibre_card
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) [IsFinite f.left]
    (hg : f.left (genericPoint X.left) = genericPoint Y.left)
    (U : Y.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [Nonempty (f.left ⁻¹ᵁ U)] [Etale (f.left ∣_ U)]
    (y : ComplexPoint (openScheme Y U)) :
    a1p_degree f.left (genericPoint X.left) =
      Nat.card ((Point.map f) ⁻¹' {Point.map (openInclusion Y U) y}) := by
  exact (properCycle_generic_residue_degree_eq_functionField_degree f hg).trans
    (s2e_c1_actual_fieldDegree_eq_etale_chart_fibre_card X Y f hg U hU y)

end HodgeLean.Foundations.QuotientDuality
