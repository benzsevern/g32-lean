import HodgeLean.Foundations.Program.CycleFoundationsPullbackSpan

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
attribute [local irreducible] cupProductOf algebraicCycleClassSpan homPullback
namespace HodgeLean.Foundations.Program
theorem cfd_hom_pullback_span_aux (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (f : B ⟶ A) [IsMonHom f] (p : ℕ)
    (x : HQ A (2 * p)) (hx : x ∈ cfd_cycleSpan A p) :
    homPullback f (2 * p) x ∈ cfd_cycleSpan B p := by
  exact cfd_morphism_pullback_span A B f p x hx

end HodgeLean.Foundations.Program
