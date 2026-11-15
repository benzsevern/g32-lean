import HodgeLean.Foundations.AbelianQuotient.Product
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.AbelianQuotient

/-- A quasi-compact morphism out of a reduced scheme has a radical image ideal. -/
theorem radical_image_kernel {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] :
    f.ker.radical = f.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  exact Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot.comap (f := (f.app U).hom))

/-- The canonical image of a quasi-compact map from a reduced scheme is reduced. -/
theorem reduced_scheme_image {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] :
    IsReduced f.image := by
  have h : ∀ U : Y.affineOpens, IsReduced (f.ker.subschemeCover.openCover.X U) := fun U => by
    have hrad : (f.ker.ideal U).radical = f.ker.ideal U := by
      simpa only [Scheme.IdealSheafData.radical_ideal] using
        congrArg (fun I : Y.IdealSheafData => I.ideal U) (radical_image_kernel f)
    have : _root_.IsReduced (Γ(Y, U.1) ⧸ f.ker.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_eq_iff.mp hrad)
    change IsReduced (Spec (CommRingCat.of (Γ(Y, U.1) ⧸ f.ker.ideal U)))
    infer_instance
  exact @IsReduced.of_openCover _ f.ker.subschemeCover.openCover h

/-- The canonical image of a quasi-compact map from an integral scheme is integral. -/
theorem integral_scheme_image {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f] [IsIntegral X] :
    IsIntegral f.image := by
  letI := reduced_scheme_image f
  have hr := ((IrreducibleSpace.isIrreducible_univ X).image f.toImage
    f.toImage.continuous.continuousOn).closure
  rw [Set.image_univ, f.toImage.denseRange.closure_range] at hr
  letI := (irreducibleSpace_def f.image).mpr hr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- A proper morphism maps onto its canonical scheme image. -/
theorem surjective_to_scheme_image {X Y : Scheme} (f : X ⟶ Y) [IsProper f] :
    Surjective f.toImage := by
  haveI : IsProper (f.toImage ≫ f.imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  haveI : IsProper f.toImage := IsProper.of_comp f.toImage f.imageι
  refine ⟨Set.range_eq_univ.mp ?_⟩
  rw [← f.toImage.isClosedMap.isClosed_range.closure_eq]
  exact f.toImage.denseRange.closure_range

end HodgeLean.Foundations.AbelianQuotient
