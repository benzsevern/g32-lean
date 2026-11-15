import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainComplexEpi
import HodgeLean.Foundations.RationalHomologyManifold.AmbientKernelSheafInclusion
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! The actual sheafified ambient cochain restriction as the cokernel of its local kernel.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual sheafified local-kernel inclusion has zero composite with actual ambient cochain restriction.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; sheafification of the actual kernel equation.
HC no distance; AV milestone no distance.
-/
theorem ambientLocalZeroSheafInclusion_restriction (X : TopCat.{0}) :
    ambientLocalZeroSheafInclusion X ≫ ambientCochainSheafRestriction X = 0 := by
  let F := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).mapHomologicalComplex
    (ComplexShape.up ℕ)
  change F.map (kernel.ι (ambientCochainPresheafComplexRestriction X)) ≫
    F.map (ambientCochainPresheafComplexRestriction X) = 0
  rw [← F.map_comp, kernel.condition, F.map_zero]

#print axioms ambientLocalZeroSheafInclusion_restriction
end HodgeLean.Foundations.RationalHomologyManifold
