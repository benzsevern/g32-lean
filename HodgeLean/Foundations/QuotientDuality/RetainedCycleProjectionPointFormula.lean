import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionValues

/-! The actual point formula of the finite projective projection. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Adapters HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified algebraic projection acts on actual points by the retained matrix.
Source: Hartshorne, Algebraic Geometry, II.7. -/
lemma retained_presentation_projection_point_formula
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (D : ProjectiveSpace.Presentation X.hom) {m : ℕ}
    (ℓ : Matrix (Fin (m+1)) (Fin (D.ambientDimension+1)) ℂ)
    (hfin : ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp
      (a3r_lin ℓ).toRingHom).Finite)
    (x : X.left) (v : CoordinateSpace D.ambientDimension) (hv : v ≠ 0)
    (hx : D.immersion x = (vectorToComplexPoint v hv).underlying) :
    retained_presentation_π X D hfin x =
      (vectorToComplexPoint (ℓ.mulVec v)
        (retained_presentation_vector_not_kernel X D ℓ hfin x v hv hx)).underlying := by
  let w := ℓ.mulVec v
  let hw := retained_presentation_vector_not_kernel X D ℓ hfin x v hv hx
  apply (a3m_projCharts m).prime_injective
  let A : HomogeneousIdeal (homogeneousSubmodule (Fin (m+1)) ℂ) :=
    ⟨_, (a3m_projCharts m).isHomogeneous_prime (retained_presentation_π X D hfin x)⟩
  let B : HomogeneousIdeal (homogeneousSubmodule (Fin (m+1)) ℂ) :=
    ⟨_, (a3m_projCharts m).isHomogeneous_prime (vectorToComplexPoint w hw).underlying⟩
  change A.toIdeal = B.toIdeal
  apply congrArg HomogeneousIdeal.toIdeal
  apply HomogeneousIdeal.ext'
  intro d p hp
  change p ∈ (a3m_projCharts m).prime (retained_presentation_π X D hfin x) ↔
    p ∈ (a3m_projCharts m).prime (vectorToComplexPoint w hw).underlying
  rw [retained_presentation_prime_π, Ideal.mem_comap,
    retained_presentation_prime_at_vector X D x v hv hx _
      (a3h_lin_isHomogeneous ℓ hp), retained_projective_prime_evaluation w hw p hp]
  exact Iff.of_eq (congrArg (fun z : ℂ => z = 0)
    (RingHom.congr_fun (retained_projection_substitution_eval ℓ v) p))

end HodgeLean.Foundations.QuotientDuality
