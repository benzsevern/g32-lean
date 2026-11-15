import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionPointFormula
import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionCentre

/-! The original embedding avoids the actual finite projection centre. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.QuotientDuality

/-- The original projective embedding with its original complex base. -/
def retained_presentation_embedding_over
    (X : Over (Spec ↧ℂ)) (D : ProjectiveSpace.Presentation X.hom) :
    X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (D.ambientDimension+1)) (Spec ↧ℂ)) :=
  Over.homMk D.immersion D.immersion_toBase

/-- The original embedded source misses the actual algebraic centre of finite parameters.
Source: Hartshorne, Algebraic Geometry, II.7. -/
lemma retained_presentation_embedding_avoids_centre
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (D : ProjectiveSpace.Presentation X.hom) {m : ℕ}
    (ℓ : Matrix (Fin (m+1)) (Fin (D.ambientDimension+1)) ℂ)
    (hfin : ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp
      (a3r_lin ℓ).toRingHom).Finite) (v : ComplexPoint X) :
    (Point.map (retained_presentation_embedding_over X D) v).underlying ∉
      retained_projection_centre ℓ := by
  letI : IsClosedImmersion D.immersion := D.isClosedImmersion
  intro h
  obtain ⟨i, hi⟩ := retained_presentation_exists_notMem X D ℓ hfin v.underlying
  apply hi
  change a3r_lin ℓ (MvPolynomial.X i) ∈
    ((a3m_projCharts D.ambientDimension).restrict D.immersion).prime v.underlying
  rw [a3m_SpecCharts.restrict_prime]
  exact h i

end HodgeLean.Foundations.QuotientDuality
