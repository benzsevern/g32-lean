import HodgeLean.Foundations.Program.CycleFoundationsDefs

/-! # Bodies of the second stage of the G32 contraction

One auxiliary body per statement of `G32ContractionTwo.lean`. HC no distance; AV milestone no
distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option Elab.async false

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program


theorem g32c_cycleSpan_eq (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) :
    cfd_cycleSpan X p = algebraicCycleClassSpan X p := by
  ext x
  rw [cfd_cycleSpan, Submodule.mem_comap]
  rfl


end HodgeLean.Foundations.Program
