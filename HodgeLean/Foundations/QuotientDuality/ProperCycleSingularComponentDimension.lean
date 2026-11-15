import HodgeLean.Foundations.QuotientDuality.ProperCycleDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.Dimension

/-! # Actual prime support dimension without an ambient smoothness premise -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- A middle-codimension prime in an integral finite-type complex scheme has the required support dimension without ambient smoothness.
Source: EGA IV, 5.6.5, dimension formula for finite-type schemes over a field.
HC no distance; AV milestone no distance. -/
lemma properCycle_middle_component_dimension
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2 * k)
    (x : X.left) (hcodim : Order.coheight x = k) :
    topologicalKrullDim (cycleComponent X.left x) = (k : ℕ) := by
  obtain ⟨-, m, hm, -⟩ := a1d_height_eq_trdeg x
  have he := a2r_height_add_coheight X x
  rw [properCycle_height_generic X, hdim, hcodim, hm] at he
  have hnat : m + k = 2 * k := by exact_mod_cast he
  have hmk : m = k := by omega
  rw [topologicalKrullDim_cycleComponent, hm, hmk]
  rfl

end HodgeLean.Foundations.QuotientDuality
