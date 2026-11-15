import HodgeLean.Foundations.Program.SchoenCycleSubalgebraEvaluationPoint

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Identifying the actual affine subalgebra prime retains the full original complex evaluations of all original subalgebra functions.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_identified_subalgebra_point_evaluation
    (X : Over (Spec ↧ℂ)) (W : X.left.Opens) (hW : IsAffineOpen W)
    (x : ComplexPoint X) (hx : ⊤ ≤ x.left ⁻¹ᵁ W) :
    letI := s2e_step1_sectionAlgebra X W
    ∀ (S : Subalgebra ℂ Γ(X.left, W))
      (z : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap S))),
      z.underlying.asIdeal = ((hW.primeIdealOf ⟨x.underlying, hx trivial⟩).asIdeal).under S →
      ∀ s : S, ComplexPoint.affineSpecEquiv S z s = Point.evaluate W s.val x := by
  letI := s2e_step1_sectionAlgebra X W
  intro S z hz s
  let ε := (s2e_step1_pointEvaluation X W x hx).comp S.val
  have hkerz : RingHom.ker (ComplexPoint.affineSpecEquiv S z).toRingHom = z.underlying.asIdeal := by
    have h := s2e_affine_spec_point_prime S (ComplexPoint.affineSpecEquiv S z)
    simpa only [Equiv.symm_apply_apply] using h.symm
  have hkerε : RingHom.ker ε.toRingHom =
      ((hW.primeIdealOf ⟨x.underlying, hx trivial⟩).asIdeal).under S := by
    rw [← s2e_affine_spec_point_prime S ε]
    exact s2e_subalgebra_evaluation_point_prime X W hW x hx S
  have he : ComplexPoint.affineSpecEquiv S z = ε :=
    s2e_complex_evaluation_eq_of_ker_eq S _ _ (hkerz.trans (hz.trans hkerε.symm))
  rw [he]
  have hv := congrArg (fun r : Γ(X.left, W) →+* ℂ => r s.val)
    (s2e_pointEvaluation_stalk_factor X W x hx)
  have hxm : x.underlying ∈ W := hx trivial
  rw [Point.evaluate, dif_pos hxm]
  exact hv

#print axioms s2e_identified_subalgebra_point_evaluation
end HodgeLean.Foundations.Program
