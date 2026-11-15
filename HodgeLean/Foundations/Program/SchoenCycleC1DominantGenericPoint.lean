import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Dominance of the actual scheme projection identifies its specified
source generic point with the original target generic point. -/
theorem s2e_c1_dominant_generic_point
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at h
  exact h.eq (genericPoint_spec Y)

end HodgeLean.Foundations.Program
