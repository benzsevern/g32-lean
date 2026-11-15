import HodgeLean.Foundations.Program.CycleFoundationsSpansProofs

/-! Projection and correspondence span transport from explicit smooth projective
abelian-variety instances and a supplied rational top coordinate.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
/-- Projection integration preserves the algebraic span for any fibre dimension.
The arbitrary rational coordinate changes geometric pushforward by a nonzero rational scalar.
Source: Fulton, Intersection Theory, second edition, §1.4 (proper pushforward), §19.1 (cycle map); Birkenhake–Lange, §1.3. -/
theorem cfd_projection_span (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (s q : ℕ) (h : 2 * s = 2 * q + 2 * d)
    (x : HQ (A ⊗ B) (2 * s)) (hx : x ∈ cfd_cycleSpan (A ⊗ B) s) :
    cfd_projection A B d I (2 * q) (HQ.castEquiv (A ⊗ B) h x) ∈
      cfd_cycleSpan A q :=
  cfd_projection_span_aux A B d hB I s q h x hx

example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (s q : ℕ) (h : 2 * s = 2 * q + 2 * d)
    (x : HQ (A ⊗ B) (2 * s)) (hx : x ∈ cfd_cycleSpan (A ⊗ B) s) :
    cfd_projection A B d I (2 * q) (HQ.castEquiv (A ⊗ B) h x) ∈
      cfd_cycleSpan A q := cfd_projection_span A B d hB I s q h x hx

/-- An algebraic correspondence class acts on HQ and preserves the algebraic span.
Source: Fulton, Intersection Theory, second edition, §16.1 (correspondences), §8.1 and §19.1. -/
theorem cfd_correspondence_span (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (c p q : ℕ) (h : 2 * c + 2 * p = 2 * q + 2 * d)
    (ξ : HQ (A ⊗ B) (2 * c)) (hξ : ξ ∈ cfd_cycleSpan (A ⊗ B) c)
    (x : HQ B (2 * p)) (hx : x ∈ cfd_cycleSpan B p) :
    cfd_corrAction A B d I c p q h ξ x ∈ cfd_cycleSpan A q :=
  cfd_correspondence_span_aux A B d hB I c p q h ξ hξ x hx

example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (hB : TopologicalSpace.dim B.left = d)
    (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ)
    (c p q : ℕ) (h : 2 * c + 2 * p = 2 * q + 2 * d)
    (ξ : HQ (A ⊗ B) (2 * c)) (hξ : ξ ∈ cfd_cycleSpan (A ⊗ B) c)
    (x : HQ B (2 * p)) (hx : x ∈ cfd_cycleSpan B p) :
    cfd_corrAction A B d I c p q h ξ x ∈ cfd_cycleSpan A q := cfd_correspondence_span A B d hB I c p q h ξ hξ x hx


end HodgeLean.Foundations.Program
