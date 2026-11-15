import HodgeLean.Foundations.QuotientDuality.RetainedCycleAnalyticProjection
import HodgeLean.Foundations.QuotientDuality.RetainedCyclePresentationProjection
import HodgeLean.Foundations.QuotientDuality.RetainedCycleFiniteProjectionDegree
import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionEmbedding
import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionComplementMap

/-! # The scheme and continuous projections on the original presentation -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The original projective presentation as a morphism over the complex base.
Source: ProjectiveSpace.Presentation.immersion_toBase.
-/
def retainedPresentationInclusion (X : Over (Spec ↧ℂ))
    (D : ProjectiveSpace.Presentation X.hom) :
    X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (D.ambientDimension+1)) (Spec ↧ℂ)) :=
  Over.homMk D.immersion D.immersion_toBase

/-- The actual presented variety avoids the actual algebraic centre of its finite projection. -/
lemma retained_presentation_image_avoids_centre
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (D : ProjectiveSpace.Presentation X.hom) {n : ℕ}
    {ℓ : Matrix (Fin (n+1)) (Fin (D.ambientDimension+1)) ℂ}
    (hfin : ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp
      (a3r_lin ℓ).toRingHom).Finite) (x : ComplexPoint X) :
    (Point.map (retainedPresentationInclusion X D) x).underlying ∉ retainedProjectionCentre ℓ := by
  letI : IsClosedImmersion D.immersion := D.isClosedImmersion
  change ¬ ∀ i, a3r_lin ℓ (MvPolynomial.X i) ∈
    (a3m_projCharts D.ambientDimension).prime (D.immersion x.underlying)
  intro h
  obtain ⟨i, hi⟩ := retained_presentation_exists_notMem X D ℓ hfin x.underlying
  apply hi
  change a3r_lin ℓ (MvPolynomial.X i) ∈
    ((a3m_projCharts D.ambientDimension).restrict D.immersion).prime x.underlying
  rw [a3m_SpecCharts.restrict_prime]
  exact h i

/-- The original finite scheme projection agrees with the literal continuous projection on actual complex points. -/
lemma retained_presentation_projection_complex_square
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (D : ProjectiveSpace.Presentation X.hom) {n : ℕ}
    {ℓ : Matrix (Fin (n+1)) (Fin (D.ambientDimension+1)) ℂ}
    (hfin : ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp
      (a3r_lin ℓ).toRingHom).Finite) (x : ComplexPoint X) :
    retainedAnalyticProjection ℓ
      ⟨Point.map (retainedPresentationInclusion X D) x,
        retained_presentation_image_avoids_centre X D hfin x⟩ =
    Point.map (show X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (n+1)) (Spec ↧ℂ)) from
      Over.homMk (retained_presentation_π X D hfin) (retained_presentation_π_fst X D hfin)) x := by
  letI : IsClosedImmersion D.immersion := D.isClosedImmersion
  obtain ⟨⟨v, hv⟩, he⟩ := surjective_vectorToComplexPoint (Point.map (retainedPresentationInclusion X D) x)
  change vectorToComplexPoint v hv = Point.map (retainedPresentationInclusion X D) x at he
  have ha : (vectorToComplexPoint v hv).underlying ∉ retainedProjectionCentre ℓ := by
    rw [he]
    exact retained_presentation_image_avoids_centre X D hfin x
  have hw : ℓ.mulVec v ≠ 0 := by
    have h := (retained_projection_centre_complement_domain ℓ (Projectivization.mk ℂ v hv)).mp ha
    exact (retained_projective_projection_domain_mk (retainedProjectionLinearMap ℓ) v hv).mp h
  have hpoint : (⟨Point.map (retainedPresentationInclusion X D) x,
      retained_presentation_image_avoids_centre X D hfin x⟩ :
      {p : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (D.ambientDimension+1)) (Spec ↧ℂ))) |
        p.underlying ∉ retainedProjectionCentre ℓ}) = ⟨vectorToComplexPoint v hv, ha⟩ :=
    Subtype.ext he.symm
  rw [hpoint, retained_analytic_projection_vector ℓ v hv hw ha]
  apply ComplexPoint.underlying_injective_of_locallyOfFiniteType
  apply (a3m_projCharts n).prime_injective
  rw [retained_projective_linear_prime]
  change ((a3m_projCharts D.ambientDimension).prime (vectorToComplexPoint v hv).underlying).comap
      (a3r_lin ℓ) = (a3m_projCharts n).prime (retained_presentation_π X D hfin x.underlying)
  rw [retained_presentation_prime_π]
  have hu : (vectorToComplexPoint v hv).underlying = D.immersion x.underlying :=
    congrArg Point.underlying he
  rw [hu]
  dsimp only [retained_presentation_charts]
  rw [a3m_SpecCharts.restrict_prime]
  rfl

end HodgeLean.Foundations.QuotientDuality


/-! The actual algebraic and continuous finite projection square. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The continuous centre-complement projection agrees with the specified algebraic projection on the original embedded source.
Source: Hartshorne, Algebraic Geometry, II.7. -/
lemma retained_presentation_projection_square
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (D : ProjectiveSpace.Presentation X.hom) {m : ℕ}
    (ℓ : Matrix (Fin (m+1)) (Fin (D.ambientDimension+1)) ℂ)
    (hfin : ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp
      (a3r_lin ℓ).toRingHom).Finite) (v : ComplexPoint X) :
    retained_projection_complement_map ℓ
      ⟨Point.map (retained_presentation_embedding_over X D) v,
        retained_presentation_embedding_avoids_centre X D ℓ hfin v⟩ =
      Point.map (retained_presentation_projection_over X D hfin) v := by
  let e := s2e_projectivePointHomeomorph D.ambientDimension
  obtain ⟨p, hp⟩ := e.surjective (Point.map (retained_presentation_embedding_over X D) v)
  induction p using Projectivization.ind with
  | h w hw =>
    change vectorToComplexPoint w hw = Point.map (retained_presentation_embedding_over X D) v at hp
    have hav : (vectorToComplexPoint w hw).underlying ∉ retained_projection_centre ℓ := by
      rw [hp]
      exact retained_presentation_embedding_avoids_centre X D ℓ hfin v
    have harg : (⟨Point.map (retained_presentation_embedding_over X D) v,
        retained_presentation_embedding_avoids_centre X D ℓ hfin v⟩ :
        {p : ComplexPoint (Over.mk (ProjectiveSpace.toBase
          (Fin (D.ambientDimension+1)) (Spec ↧ℂ))) |
          p.underlying ∉ retained_projection_centre ℓ}) = ⟨vectorToComplexPoint w hw, hav⟩ :=
      Subtype.ext hp.symm
    rw [harg, retained_projection_complement_map_vector]
    apply ComplexPoint.underlying_injective_of_locallyOfFiniteType
    have hx : D.immersion v.underlying = (vectorToComplexPoint w hw).underlying :=
      congrArg Point.underlying hp.symm
    exact (retained_presentation_projection_point_formula X D ℓ hfin v.underlying w hw hx).symm

end HodgeLean.Foundations.QuotientDuality
