import HodgeLean.Foundations.QuotientDuality.RetainedCyclePresentationNoether
import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedComponentHomology
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingularComponentDimension

/-! Prime presentations inherited from the original ambient embedding. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.QuotientDuality

/-- Present the actual reduced component using the original ambient closed immersion. -/
def retained_component_projective_presentation
    (X : Over (Spec ↧ℂ)) (D : ProjectiveSpace.Presentation X.hom) (ξ : X.left) :
    ProjectiveSpace.Presentation (properCycle_component_over X ξ).hom :=
  { ambientDimension := D.ambientDimension
    immersion := cycleComponentι X.left ξ ≫ D.immersion
    isClosedImmersion := by
      letI : IsClosedImmersion D.immersion := D.isClosedImmersion
      infer_instance
    immersion_toBase := by
      rw [Category.assoc, D.immersion_toBase]
      rfl }

/-- Finite Noether parameters for a middle prime can be chosen in its original ambient coordinates. -/
lemma retained_component_finite_linear_forms
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (D : ProjectiveSpace.Presentation X.hom) (k : ℕ)
    (hdim : TopologicalSpace.dim X.left = 2*k) (ξ : X.left) (hc : Order.coheight ξ = k) :
    ∃ ℓ : Matrix (Fin (k+1)) (Fin (D.ambientDimension+1)) ℂ,
      ((Ideal.Quotient.mk (retained_presentation_cone_ideal (properCycle_component_over X ξ)
        (retained_component_projective_presentation X D ξ))).comp (a3r_lin ℓ).toRingHom).Finite := by
  exact retained_presentation_finite_linear_forms (properCycle_component_over X ξ)
    (retained_component_projective_presentation X D ξ) k
    (properCycle_middle_component_dimension X k hdim ξ hc)

end HodgeLean.Foundations.QuotientDuality
