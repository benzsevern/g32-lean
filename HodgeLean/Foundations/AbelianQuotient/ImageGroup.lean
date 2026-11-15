import HodgeLean.Foundations.AbelianQuotient.ImageOperations
import HodgeLean.Foundations.AbelianQuotient.GroupSubobject
import HodgeLean.Foundations.AbelianQuotient.SmoothGroup

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open CategoryTheory.MonoidalCategory
open HodgeLean.Foundations
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- The canonical image carries a group structure making inclusion and factor homomorphisms. -/
theorem canonical_image_group {A B : Variety} (f : Hom A B) :
    ∃ G : GrpObj (imageModel f), letI := G
      IsMonHom (imageInclusion f) ∧ IsMonHom (imageFactor f) := by
  let i := imageInclusion f
  let p := imageFactor f
  haveI : IsClosedImmersion i.left := by
    change IsClosedImmersion f.hom.left.imageι
    infer_instance
  haveI : Mono i := Over.mono_of_mono_left i
  have hpi : p ≫ i = f.hom := by
    apply Over.OverMorphism.ext
    exact Scheme.Hom.toImage_imageι f.hom.left
  obtain ⟨m, hm⟩ := image_multiplication_lift f
  obtain ⟨v, hv⟩ := image_inverse_lift f
  have he : (η[A.X] ≫ p) ≫ i = η[B.X] := by
    rw [Category.assoc, hpi]
    exact IsMonHom.one_hom f.hom
  obtain ⟨G, hG⟩ := group_subobject i (η[A.X] ≫ p) m v he hm hv
  letI := G
  letI := hG
  haveI : IsMonHom (p ≫ i) := by
    rw [hpi]
    infer_instance
  exact ⟨G, hG, isMonHom_of_mono_comp p i⟩

/-- The canonical scheme image is an abelian variety with its actual factorization. -/
theorem canonical_image_abelian {A B : Variety} (f : Hom A B) :
    ∃ G : GrpObj (imageModel f),
      letI := G
      IsCommMonObj (imageModel f) ∧ IsIntegral (imageModel f).left ∧
      Smooth (imageModel f).hom ∧ IsProjective (imageModel f).hom ∧
      IsMonHom (imageFactor f) ∧ IsMonHom (imageInclusion f) ∧
      Function.Surjective (Point.map (imageFactor f)) := by
  obtain ⟨G, hi, hp⟩ := canonical_image_group f
  letI := G
  obtain ⟨hInt, hProj, hSurj⟩ := canonical_image_geometry f
  letI := hInt
  letI := hProj
  have hComm : IsCommMonObj (imageModel f) :=
    isCommMonObj_of_complexSelfProductIntegral (imageModel f)
      (complexSelfProductIntegral_of_isIntegral (imageModel f))
  haveI : GrpObj (Over.mk (imageModel f).hom) := by
    change GrpObj (imageModel f)
    exact G
  have hSmooth : Smooth (imageModel f).hom := smooth_complex_group (imageModel f).hom
  exact ⟨G, hComm, hInt, hSmooth, hProj, hp, hi, hSurj⟩

end HodgeLean.Foundations.AbelianQuotient
