import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveImage

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The subscheme cut out by the vanishing ideal of a closed set is reduced.
Source: the radicality of vanishing ideals on affine spectra and locality of reducedness. -/
theorem s0_vanishing_subscheme_reduced (X : Scheme.{0}) (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have h : ∀ U : X.affineOpens, IsReduced (I.subschemeCover.openCover.X U) := fun U ↦ by
    have : _root_.IsReduced (Γ(X, U.1) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (PrimeSpectrum.isRadical_vanishingIdeal _)
    change IsReduced (Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U)))
    infer_instance
  exact @IsReduced.of_openCover _ I.subschemeCover.openCover h

#print axioms s0_vanishing_subscheme_reduced
end HodgeLean.Foundations.Program
