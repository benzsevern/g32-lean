import HodgeLean.Foundations.AbelianQuotient.ImageGeometry
import HodgeLean.Foundations.Analytic.Analytification
import HodgeLean.Foundations.Analytic.AnalytificationChowProjective

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations
namespace HodgeLean.Foundations.AbelianQuotient

/-- Algebraic maps between the retained projective varieties are proper. -/
theorem proper_hom {A B : Variety} (f : Hom A B) : IsProper f.hom.left := by
  haveI : IsProper (f.hom.left ≫ B.X.hom) := by
    rw [Over.w]
    infer_instance
  exact IsProper.of_comp f.hom.left B.X.hom

/-- The canonical image is integral and projective, and its factor is onto on complex points. -/
theorem canonical_image_geometry {A B : Variety} (f : Hom A B) :
    IsIntegral (imageModel f).left ∧ IsProjective (imageModel f).hom ∧
      Function.Surjective (Point.map (imageFactor f)) := by
  letI := proper_hom f
  letI := surjective_to_scheme_image f.hom.left
  refine ⟨integral_scheme_image f.hom.left, ?_, ?_⟩
  · exact Analytic.AnalytificationChow_isProjective_comp_of_isClosedImmersion
      f.hom.left.imageι B.X.hom
  · haveI : Surjective (imageFactor f).left := by
      change Surjective f.hom.left.toImage
      infer_instance
    exact Analytic.f4_map_surjective (imageFactor f)

end HodgeLean.Foundations.AbelianQuotient
