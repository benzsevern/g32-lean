import HodgeLean.Foundations.Program.SchoenTransferJ12Projection
import Mathlib.AlgebraicGeometry.Morphisms.Separated

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
namespace HodgeLean.Foundations.Program

/-- The actual target-first graph is a closed immersion over the separated target.
Source: Hartshorne, Algebraic Geometry, II, Exercise 4.8; Mathlib IsClosedImmersion.of_comp. -/
theorem s4_selected_graph_closed_immersion
    (A Y : Over (Spec ↧ℂ)) [IsSeparated A.hom] (f : Y ⟶ A) :
    IsClosedImmersion (lift f (𝟙 Y)).left := by
  letI : IsSeparated (snd A Y).left := by
    change IsSeparated (Limits.pullback.snd A.hom Y.hom)
    infer_instance
  have hcomp : (lift f (𝟙 Y)).left ≫ (snd A Y).left = 𝟙 Y.left := by
    exact congrArg Over.Hom.left (lift_snd f (𝟙 Y))
  letI : IsClosedImmersion ((lift f (𝟙 Y)).left ≫ (snd A Y).left) := by
    rw [hcomp]
    infer_instance
  exact IsClosedImmersion.of_comp (lift f (𝟙 Y)).left (snd A Y).left

#print axioms s4_selected_graph_closed_immersion

end HodgeLean.Foundations.Program
