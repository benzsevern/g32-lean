import HodgeLean.Foundations.QuotientDuality.RetainedCycleFiniteProjectionCriterion
import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionSquare
import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionDominance
import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionCentreCoheight

/-! # Nonvanishing of the actual intrinsic class in a projective embedding -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual intrinsic top class has nonzero image in every specified projective embedding. -/
lemma retained_projective_presentation_image_nonzero
    (V : Over (Spec ↧ℂ)) [IsIntegral V.left] [IsProjective V.hom]
    (D : ProjectiveSpace.Presentation V.hom) (d : ℕ)
    (hdim : topologicalKrullDim V.left = (d : ℕ)) :
    homologyMap ℚ (2*d) (TopCat.ofHom (Point.continuousMap (retainedPresentationInclusion V D)))
      (properCycle_intrinsic_class V d hdim) ≠ 0 := by
  let P := a3h_PnO D.ambientDimension
  let W := a3h_PnO d
  letI (r : ℕ) : IsProjective (a3h_PnO r).hom :=
    ⟨⟨{ ambientDimension := r,
         immersion := 𝟙 _,
         isClosedImmersion := inferInstance,
         immersion_toBase := Category.id_comp _ }⟩⟩
  letI : IsIntegral W.left := IntersectionProductScaf_projective_integral d
  letI : Smooth P.hom := IntersectionProductScaf_projective_smooth D.ambientDimension
  obtain ⟨ℓ, hfin, hb⟩ := retained_presentation_finite_forms_with_centre_bound V D d hdim
  let f : V ⟶ W := Over.homMk (retained_presentation_π V D hfin)
    (retained_presentation_π_fst V D hfin)
  letI : IsProper f.left := retained_presentation_π_isProper V D hfin
  exact retained_intrinsic_image_ne_zero_of_projection V W P d hdim
    (s0_complex_projective_krull_dimension d) (retainedPresentationInclusion V D)
    (retainedProjectionCentre ℓ)
    (fun p hp => retained_projection_centre_coheight ℓ hb p hp)
    (retained_presentation_image_avoids_centre V D hfin)
    (TopCat.ofHom (retainedAnalyticProjection ℓ)) f
    (retained_presentation_projection_generic V D hfin
      (retained_presentation_cone_dimension V D d hdim))
    (retained_presentation_projection_degree_pos V D hfin)
    (retained_presentation_projection_complex_square V D hfin)

end HodgeLean.Foundations.QuotientDuality
