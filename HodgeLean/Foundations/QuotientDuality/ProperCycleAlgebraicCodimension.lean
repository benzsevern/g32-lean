import HodgeLean.Foundations.QuotientDuality.ProperCycleSingularComponentDimension
import HodgeLean.Adapters.NormalConeB4aGysinReducedClosedDimension
import HodgeLean.Adapters.NormalConeB4aGysinSupportDimension

/-! # Actual closed-support dimension bounds from codimension without smoothness -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- A lower codimension bound controls the actual closed-support dimension in an integral finite-type ambient scheme.
Source: EGA IV, 5.6.5, dimension formula;
Bredon, Sheaf Theory, second edition, V.9, algebraic dimension bounds for supports.
HC no distance; AV milestone no distance. -/
lemma properCycle_closed_support_dimension_le_of_coheight
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (S : Closeds X.left) (c : ℕ)
    (hc : ∀ z ∈ S, (c : ℕ∞) ≤ Order.coheight z) :
    topologicalKrullDim S ≤ (TopologicalSpace.dim X.left - c : ℕ) := by
  have hD : topologicalKrullDim X.left = (TopologicalSpace.dim X.left : ℕ) := by
    rw [Scheme.topologicalKrullDim_eq_orderKrullDim, ← Order.height_top_eq_krullDim]
    change (↑(Order.height (genericPoint X.left)) : WithBot ℕ∞) = _
    rw [properCycle_height_generic X]
    rfl
  have hs := a3b4a_gysin_support_dimension_of_ambient_bound (TopologicalSpace.dim X.left) c S hD.le hc
  rw [a3b4a_gysin_reduced_closed_dimension_eq] at hs
  exact hs

end HodgeLean.Foundations.QuotientDuality
