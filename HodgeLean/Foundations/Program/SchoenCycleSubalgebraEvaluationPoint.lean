import HodgeLean.Foundations.Program.SchoenCycleAffineSpecPointPrime
import HodgeLean.Foundations.Program.SchoenCyclePointIdealStabilizer

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Restricting the actual affine evaluation to a subalgebra constructs a complex point with exactly the contracted actual prime.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_subalgebra_evaluation_point_prime
    (X : Over (Spec ↧ℂ)) (W : X.left.Opens) (hW : IsAffineOpen W)
    (x : ComplexPoint X) (hx : ⊤ ≤ x.left ⁻¹ᵁ W) :
    letI := s2e_step1_sectionAlgebra X W
    ∀ S : Subalgebra ℂ Γ(X.left, W),
      ((ComplexPoint.affineSpecEquiv S).symm
        ((s2e_step1_pointEvaluation X W x hx).comp S.val)).underlying.asIdeal =
      ((hW.primeIdealOf ⟨x.underlying, hx trivial⟩).asIdeal).under S := by
  letI := s2e_step1_sectionAlgebra X W
  intro S
  rw [s2e_affine_spec_point_prime]
  change (RingHom.ker (s2e_step1_pointEvaluation X W x hx).toRingHom).comap S.val.toRingHom = _
  rw [s2e_pointEvaluation_kernel_primeIdealOf X W hW x hx]
  rfl

#print axioms s2e_subalgebra_evaluation_point_prime
end HodgeLean.Foundations.Program
