import HodgeLean.Foundations.Program.CycleFoundationsPullbackSpansProofs

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
/-- Every abelian-variety homomorphism preserves the rational algebraic span by pullback.
Source: Fulton, Intersection Theory, second edition, §8.1 (pullback between smooth varieties) and §19.1 (cycle map). -/
theorem cfd_hom_pullback_span (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (f : B ⟶ A) [IsMonHom f] (p : ℕ)
    (x : HQ A (2 * p)) (hx : x ∈ cfd_cycleSpan A p) :
    homPullback f (2 * p) x ∈ cfd_cycleSpan B p :=
  cfd_hom_pullback_span_aux A B f p x hx

example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (f : B ⟶ A) [IsMonHom f] (p : ℕ)
    (x : HQ A (2 * p)) (hx : x ∈ cfd_cycleSpan A p) :
    homPullback f (2 * p) x ∈ cfd_cycleSpan B p := cfd_hom_pullback_span A B f p x hx


end HodgeLean.Foundations.Program
