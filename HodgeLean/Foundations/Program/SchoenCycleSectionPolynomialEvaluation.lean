import HodgeLean.Foundations.Program.SchoenCyclePointIdealStabilizer

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Actual complex evaluation of a polynomial section homomorphism is evaluation in the exact values of its variable sections.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_section_polynomial_evaluate
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (σ : Type*) :
    letI := s2e_step1_sectionAlgebra X U
    ∀ (G : MvPolynomial σ ℂ →ₐ[ℂ] Γ(X.left, U))
      (q : ComplexPoint X), q.underlying ∈ U → ∀ p : MvPolynomial σ ℂ,
      Point.evaluate U (G p) q = aeval (fun i => Point.evaluate U (G (MvPolynomial.X i)) q) p := by
  letI := s2e_step1_sectionAlgebra X U
  intro G q hq p
  let hqBound := s2e_step1_point_preimage X q U hq
  let ε := s2e_step1_pointEvaluation X U q hqBound
  have hε (s : Γ(X.left, U)) : ε s = Point.evaluate U s q := by
    rw [Point.evaluate, dif_pos hq]
    exact congrArg (fun f : Γ(X.left, U) →+* ℂ => f s)
      (s2e_pointEvaluation_stalk_factor X U q hqBound)
  have he : ε.comp G = aeval (fun i => Point.evaluate U (G (MvPolynomial.X i)) q) := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X]
    exact hε _
  exact (hε (G p)).symm.trans (congrArg (fun f : MvPolynomial σ ℂ →ₐ[ℂ] ℂ => f p) he)

#print axioms s2e_section_polynomial_evaluate
end HodgeLean.Foundations.Program
