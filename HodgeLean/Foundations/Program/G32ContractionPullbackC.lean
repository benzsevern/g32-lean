import HodgeLean.Foundations.Program.G32ContractionScalar
import HodgeLean.Foundations.Program.G32ContractionCycleSpan
import HodgeLean.Foundations.Program.CycleFoundationsPullback

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


theorem g32c_pullbackC_span_aux (Y B : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (f : B ⟶ Y) [IsMonHom f] (p : ℕ) (x : ℂ ⊗[ℚ] HQ Y (2 * p))
    (hx : x ∈ (algebraicCycleClassSpan Y p).baseChange ℂ) :
    (homPullback f (2 * p)).baseChange ℂ x ∈ (algebraicCycleClassSpan B p).baseChange ℂ := by
  have hf : ∀ v ∈ algebraicCycleClassSpan Y p,
      homPullback f (2 * p) v ∈ algebraicCycleClassSpan B p := by
    intro v hv
    have hv' : v ∈ cfd_cycleSpan Y p := by rwa [g32c_cycleSpan_eq]
    have h := cfd_hom_pullback_span Y B f p v hv'
    rwa [g32c_cycleSpan_eq] at h
  exact g32c_baseChange_map_mem (homPullback f (2 * p)) _ _ hf x hx


end HodgeLean.Foundations.Program
