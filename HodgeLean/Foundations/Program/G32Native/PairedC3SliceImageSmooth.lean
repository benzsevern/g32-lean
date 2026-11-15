import HodgeLean.Ported.Hironaka.Scheme.Smooth.AdaptedCoordinates

/-! # Smooth relative dimension of the actual closed slice image -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A smooth closed slice retains its relative dimension when represented
by the subscheme of its actual kernel ideal sheaf.
Source: Hartshorne, Algebraic Geometry, II.5 and III.10. -/
theorem paired_c3_slice_image_relative_dimension
    {K : Type} [Field K]
    {Q X : Over (Spec (CommRingCat.of K))} (f : Q ⟶ X)
    [IsClosedImmersion f.left] (m : ℕ) [SmoothOfRelativeDimension m Q.hom] :
    SmoothOfRelativeDimension m (f.left.ker.subschemeι ≫ X.hom) := by
  have he : inv f.left.toImage ≫ f.left = f.left.imageι := by
    calc
      inv f.left.toImage ≫ f.left =
          inv f.left.toImage ≫ (f.left.toImage ≫ f.left.imageι) :=
        congrArg (fun h => inv f.left.toImage ≫ h) f.left.toImage_imageι.symm
      _ = f.left.imageι := by
        rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  change SmoothOfRelativeDimension m (f.left.imageι ≫ X.hom)
  rw [← he, Category.assoc, Over.w f]
  simpa only [zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + m) (inv f.left.toImage ≫ Q.hom))

#print axioms paired_c3_slice_image_relative_dimension
end HodgeLean.Foundations.Program.G32Native
