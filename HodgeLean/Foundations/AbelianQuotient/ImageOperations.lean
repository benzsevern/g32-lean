import HodgeLean.Foundations.AbelianQuotient.ProperOver
import HodgeLean.Foundations.AbelianQuotient.ImageLift

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open HodgeLean.Foundations
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- Inversion on the ambient variety restricts algebraically to the canonical image. -/
theorem image_inverse_lift {A B : Variety} (f : Hom A B) :
    ∃ v : imageModel f ⟶ imageModel f,
      v ≫ imageInclusion f = imageInclusion f ≫ ι[B.X] := by
  let H := imageModel f
  let i := imageInclusion f
  let p := imageFactor f
  obtain ⟨hInt, hProj, hSurj⟩ := canonical_image_geometry f
  letI : IsIntegral H.left := hInt
  letI : IsProjective H.hom := hProj
  haveI : IsClosedImmersion i.left := by
    change IsClosedImmersion f.hom.left.imageι
    infer_instance
  let g : H ⟶ B.X := i ≫ ι[B.X]
  letI := proper_over_map g
  have hpi : p ≫ i = f.hom := by
    apply Over.OverMorphism.ext
    exact Scheme.Hom.toImage_imageι f.hom.left
  apply lift_of_complex_points i g
  intro x
  obtain ⟨a, ha⟩ := hSurj x
  change a ≫ p = x at ha
  refine ⟨Point.map p a⁻¹, ?_⟩
  change (a⁻¹ ≫ p) ≫ i = x ≫ i ≫ ι[B.X]
  rw [Category.assoc, hpi, GrpObj.inv_comp]
  rw [← hpi, ← Category.assoc, ha]
  exact Category.assoc x i ι[B.X]

/-- Multiplication on the ambient variety restricts algebraically to the canonical image. -/
theorem image_multiplication_lift {A B : Variety} (f : Hom A B) :
    ∃ m : imageModel f ⊗ imageModel f ⟶ imageModel f,
      m ≫ imageInclusion f =
        (imageInclusion f ⊗ₘ imageInclusion f) ≫ μ[B.X] := by
  let H := imageModel f
  let i := imageInclusion f
  let p := imageFactor f
  obtain ⟨hInt, hProj, hSurj⟩ := canonical_image_geometry f
  letI : IsIntegral H.left := hInt
  letI : IsProjective H.hom := hProj
  haveI : IsClosedImmersion i.left := by
    change IsClosedImmersion f.hom.left.imageι
    infer_instance
  letI : IsIntegral (H ⊗ H).left :=
    isIntegral_pullback_of_isAlgClosed ℂ H.left H.left H.hom H.hom
  letI : IsProjective (H ⊗ H).hom := by
    change IsProjective (Limits.pullback.fst H.hom H.hom ≫ H.hom)
    exact Analytic.AnalytificationChow_isProjective_pullback H.hom H.hom
  let g : H ⊗ H ⟶ B.X := (i ⊗ₘ i) ≫ μ[B.X]
  letI := proper_over_map g
  have hpi : p ≫ i = f.hom := by
    apply Over.OverMorphism.ext
    exact Scheme.Hom.toImage_imageι f.hom.left
  have hg : g = (fst H H ≫ i) * (snd H H ≫ i) := by
    rw [Hom.mul_def]
    change (i ⊗ₘ i) ≫ μ[B.X] = lift (fst H H ≫ i) (snd H H ≫ i) ≫ μ[B.X]
    apply congrArg (fun t => t ≫ μ[B.X])
    apply hom_ext <;> simp only [tensorHom_fst, tensorHom_snd, lift_fst, lift_snd] <;> rfl
  apply lift_of_complex_points i g
  intro z
  obtain ⟨a, ha⟩ := hSurj (z ≫ fst H H)
  obtain ⟨b, hb⟩ := hSurj (z ≫ snd H H)
  change a ≫ p = z ≫ fst H H at ha
  change b ≫ p = z ≫ snd H H at hb
  have hfa : a ≫ f.hom = (z ≫ fst H H) ≫ i := by
    rw [← hpi, ← Category.assoc, ha]
  have hfb : b ≫ f.hom = (z ≫ snd H H) ≫ i := by
    rw [← hpi, ← Category.assoc, hb]
  refine ⟨Point.map p (a * b), ?_⟩
  change ((a * b) ≫ p) ≫ i = z ≫ g
  rw [Category.assoc, hpi, MonObj.mul_comp, hg, MonObj.comp_mul, hfa, hfb]
  simp only [Category.assoc]

end HodgeLean.Foundations.AbelianQuotient
