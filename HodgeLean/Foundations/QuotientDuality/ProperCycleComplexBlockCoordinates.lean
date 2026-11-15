import HodgeLean.Foundations.QuotientDuality.ProperCycleOrderedComplexRealCoordinates
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Literal ordered complex tangential and normal coordinate blocks
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual ordered complex linear coordinates split the first tangential coordinates from the remaining normal coordinates.
Source: Fin.appendEquiv; LinearEquiv.toContinuousLinearEquiv.
HC no distance; AV milestone no distance. -/
def properCycle_complex_block_coordinates (r d : ℕ) :
    (Fin (r+d) → ℂ) ≃L[ℂ] ((Fin r → ℂ) × (Fin d → ℂ)) := by
  let L : (Fin (r+d) → ℂ) ≃ₗ[ℂ] ((Fin r → ℂ) × (Fin d → ℂ)) :=
    { (Fin.appendEquiv r d).symm with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact L.toContinuousLinearEquiv

end HodgeLean.Foundations.QuotientDuality
