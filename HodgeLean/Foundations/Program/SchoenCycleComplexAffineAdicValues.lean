import HodgeLean.Foundations.Program.SchoenCycleComplexAffineAdic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Canonical complex affine formal coordinates preserve the formal value of every actual section germ.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_complex_affine_adic_of_section
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (p : X.left) (hp : p ∈ U) (hclosed : IsClosed ({p} : Set X.left))
    (s : Γ(X.left, U)) :
    letI := s2e_step1_sectionAlgebra X U
    letI : Algebra ℂ (X.left.presheaf.stalk p) := (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
    s2e_complex_affine_point_adic_equiv X U hU p hp hclosed
      (AdicCompletion.of (hU.primeIdealOf ⟨p, hp⟩).asIdeal Γ(X.left, U) s) =
      AdicCompletion.of (IsLocalRing.maximalIdeal (X.left.presheaf.stalk p))
        (X.left.presheaf.stalk p) ((X.left.presheaf.germ U p hp).hom s) := by
  apply AdicCompletion.ext
  intro n
  rfl

#print axioms s2e_complex_affine_adic_of_section
end HodgeLean.Foundations.Program
