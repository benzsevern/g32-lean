import HodgeLean.Foundations.Program.G32Native.PairedC3RatioNormalization
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-! # Smoothness of the normalized residual affine-line ruling -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- The polynomial extension of a smooth base gives a smooth projection
to the original affine line, by the actual base-change square. -/
theorem pairedC3_polynomial_projection_smooth
    (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R B)))) :
    Smooth (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap R B)))) := by
  algebraize [Polynomial.mapRingHom (algebraMap R B)]
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R B (Polynomial R) (Polynomial B))
  exact MorphismProperty.of_isPullback (P := @Smooth) sq h

/-- Translating and scaling by a variable unit preserves smoothness of
the residual ruling. This uses w = α⁻¹X - 1 as the marked-origin parameter.
Source: Hartshorne, Algebraic Geometry, II.7.13 and III.10. -/
theorem pairedC3_normalized_polynomial_projection_smooth
    (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R B)))) (α : Bˣ) :
    Smooth (Spec.map (CommRingCat.ofHom
      ((pairedC3NormalizedPolynomialEquiv α).symm.toRingEquiv.toRingHom.comp
        (Polynomial.mapRingHom (algebraMap R B))))) := by
  let e := (pairedC3NormalizedPolynomialEquiv α).symm.toRingEquiv
  letI : IsIso (CommRingCat.ofHom e.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr e.bijective
  letI := pairedC3_polynomial_projection_smooth R B h
  change Smooth (Spec.map (CommRingCat.ofHom
    (e.toRingHom.comp (Polynomial.mapRingHom (algebraMap R B)))))
  change Smooth (Spec.map
    (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap R B)) ≫
      CommRingCat.ofHom e.toRingHom))
  rw [Spec.map_comp]
  infer_instance

#print axioms pairedC3_polynomial_projection_smooth
#print axioms pairedC3_normalized_polynomial_projection_smooth
end HodgeLean.Foundations.Program.G32Native
