import HodgeLean.Adapters.IntersectionProductMovingRobertsScheme
import HodgeLean.Foundations.QuotientDuality.ProperCycleDimension

/-! Homogeneous cones for a specified ambient projective presentation. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.QuotientDuality

/-- Restrict the actual projective charts using the specified presentation. -/
def retained_presentation_charts
    (X : Over (Spec ↧ℂ)) (P : ProjectiveSpace.Presentation X.hom) :
    HodgeLean.Adapters.a3m_SpecCharts X.left (Fin (P.ambientDimension+1)) ℂ := by
  letI : IsClosedImmersion P.immersion := P.isClosedImmersion
  exact (HodgeLean.Adapters.a3m_projCharts P.ambientDimension).restrict P.immersion

/-- The actual homogeneous cone ideal in the specified ambient presentation. -/
abbrev retained_presentation_cone_ideal
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (P : ProjectiveSpace.Presentation X.hom) :=
  (retained_presentation_charts X P).prime (genericPoint X.left)

instance retained_presentation_cone_prime
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (P : ProjectiveSpace.Presentation X.hom) :
    (retained_presentation_cone_ideal X P).IsPrime :=
  (retained_presentation_charts X P).isPrime_prime _

/-- The specified presentation retains the homogeneous ideal of the generic component. -/
lemma retained_presentation_cone_homogeneous
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (P : ProjectiveSpace.Presentation X.hom) :
    (retained_presentation_cone_ideal X P).IsHomogeneous
      (homogeneousSubmodule (Fin (P.ambientDimension+1)) ℂ) :=
  (retained_presentation_charts X P).isHomogeneous_prime _

/-- Point height is the dimension of its actual cone minus one for the specified presentation. -/
lemma retained_presentation_height_add_one
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (P : ProjectiveSpace.Presentation X.hom)
    (x : X.left) :
    (Order.height x : WithBot ℕ∞) + 1 =
      ringKrullDim (MvPolynomial (Fin (P.ambientDimension+1)) ℂ ⧸
        (retained_presentation_charts X P).prime x) := by
  let _ : ∀ j, Algebra ℂ ((retained_presentation_charts X P).T j) :=
    fun j => (((retained_presentation_charts X P).θ j).comp C).toAlgebra
  exact HodgeLean.Adapters.a3m_SpecCharts.height_add_one (Y := X)
    (retained_presentation_charts X P) (fun _ _ => rfl) x

/-- The specified homogeneous cone has one dimension more than its integral projective scheme. -/
lemma retained_presentation_cone_dimension
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (P : ProjectiveSpace.Presentation X.hom) (d : ℕ)
    (hdim : topologicalKrullDim X.left = (d : ℕ)) :
    ringKrullDim (MvPolynomial (Fin (P.ambientDimension+1)) ℂ ⧸
      retained_presentation_cone_ideal X P) = (d+1 : ℕ) := by
  have hd : TopologicalSpace.dim X.left = d := by
    unfold TopologicalSpace.dim
    rw [hdim]
    rfl
  have hh : Order.height (genericPoint X.left) = (d : ℕ∞) := by
    rw [properCycle_height_generic X, hd]
  rw [← retained_presentation_height_add_one X P (genericPoint X.left), hh]
  rfl

/-- Every point in the specified projective presentation has a nonvanishing homogeneous coordinate. -/
lemma retained_presentation_relevant
    (X : Over (Spec ↧ℂ)) (P : ProjectiveSpace.Presentation X.hom) (x : X.left) :
    ∃ j, MvPolynomial.X j ∉ (retained_presentation_charts X P).prime x :=
  ⟨(retained_presentation_charts X P).chart x,
    fun h => ((retained_presentation_charts X P).X_mem_prime_iff x _).1 h
      ((retained_presentation_charts X P).mem_chart x)⟩

end HodgeLean.Foundations.QuotientDuality
