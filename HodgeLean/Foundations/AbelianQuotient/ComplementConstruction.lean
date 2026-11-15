import HodgeLean.Foundations.AbelianQuotient.ComplementAddition
import HodgeLean.Foundations.AbelianQuotient.ImageSubvariety

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- The retraction vanishes on the actual image of the difference map. -/
theorem complement_image_comp_retraction {A : Variety} (S : Subvariety A)
    (N : ℕ) (r : Hom A S.B)
    (hr : S.inclusion.hom ≫ r.hom = (multiplication S.B N).hom) :
    imageInclusion (complementMap S N r) ≫ r.hom =
      (1 : imageModel (complementMap S N r) ⟶ S.B.X) := by
  let e := complementMap S N r
  let p := imageFactor e
  let i := imageInclusion e
  obtain ⟨hInt, _, hSurj⟩ := canonical_image_geometry e
  letI := hInt
  have hpi : p ≫ i = e.hom := by
    apply Over.OverMorphism.ext
    exact Scheme.Hom.toImage_imageι e.hom.left
  have h : p ≫ i ≫ r.hom = (1 : A.X ⟶ S.B.X) := by
    rw [← Category.assoc, hpi]
    exact complement_map_comp_retraction S N r hr
  apply abq_over_hom_ext_of_point_map
  funext t
  obtain ⟨a, ha⟩ := hSurj t
  change a ≫ p = t at ha
  change t ≫ (i ≫ r.hom) = t ≫ (1 : imageModel e ⟶ S.B.X)
  rw [MonObj.comp_one, ← ha, Category.assoc, h, MonObj.comp_one]

/-- The image of the difference from a positive multiplication retraction is a complement. -/
theorem exists_complementary_subvariety {A : Variety} (S : Subvariety A) :
    ∃ T : Subvariety A, ccm2_IsogenyOnPoints (additionMap S T) := by
  obtain ⟨N, r, hN, hr⟩ := subvariety_retraction S
  let e := complementMap S N r
  let T := imageSubvariety e
  refine ⟨T, addition_isogeny_of_retraction S T N hN r hr (imageFactor e) ?_ ?_⟩
  · change imageFactor e ≫ imageInclusion e = e.hom
    apply Over.OverMorphism.ext
    exact Scheme.Hom.toImage_imageι e.hom.left
  · exact complement_image_comp_retraction S N r hr

end HodgeLean.Foundations.AbelianQuotient
