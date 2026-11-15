import HodgeLean.Foundations.Program.SchoenTowerAffineSpacePolynomial
import HodgeLean.Foundations.Program.SchoenTowerL1aEtaleCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Polynomial parameters of actual affine-space morphisms

Implication from an etale morphism to affine space to etaleness of its
actual coordinate evaluation map. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- Polynomial evaluation in the pulled-back affine coordinates is the actual map on sections in polynomial coordinates.
Source: Hartshorne, Algebraic Geometry, II.2, morphisms of affine schemes. -/
theorem s2v_l1a_affineSpace_section_polynomial_map
    (X : Over (Spec ↧ℂ)) (ι : Type)
    (f : X ⟶ Over.mk (complexAffineSpace ι ↘ Spec ↧ℂ)) :
    MvPolynomial.eval₂Hom (algebraMap ℂ Γ(X.left, ⊤))
        (fun i => f.left.appTop ((s2t_affineSpacePolynomialEquiv ι) (MvPolynomial.X i))) =
      f.left.appTop.hom.comp (s2t_affineSpacePolynomialEquiv ι).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [MvPolynomial.eval₂Hom_C]
    change algebraMap ℂ Γ(X.left, ⊤) c =
      (s2t_overSectionsAlgHom f) ((s2t_affineSpacePolynomialEquiv ι) (MvPolynomial.C c))
    rw [show MvPolynomial.C c = algebraMap ℂ (MvPolynomial ι ℂ) c from rfl,
      AlgEquiv.commutes, AlgHom.commutes]
  · intro i
    rw [MvPolynomial.eval₂Hom_X']
    rfl

/-- Etaleness of an actual affine-space morphism gives etaleness of polynomial evaluation in its pulled-back coordinates.
Source: Hartshorne, Algebraic Geometry, III.10, affine etale morphisms. -/
theorem s2v_l1a_affineSpace_section_polynomial_etale
    (X : Over (Spec ↧ℂ)) [IsAffine X.left] (ι : Type)
    (f : X ⟶ Over.mk (complexAffineSpace ι ↘ Spec ↧ℂ)) [Etale f.left] :
    (MvPolynomial.eval₂Hom (algebraMap ℂ Γ(X.left, ⊤))
      (fun i => f.left.appTop ((s2t_affineSpacePolynomialEquiv ι) (MvPolynomial.X i)))).Etale := by
  letI : IsAffine (Over.mk (complexAffineSpace ι ↘ Spec ↧ℂ)).left :=
    inferInstanceAs (IsAffine (complexAffineSpace ι))
  rw [s2v_l1a_affineSpace_section_polynomial_map]
  have hf : f.left.appTop.hom.Etale := by
    simpa only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl, op_id,
      X.left.presheaf.map_id, Category.comp_id, Scheme.Hom.appTop] using
      (Scheme.Hom.etale_appLE f.left (isAffineOpen_top _) (isAffineOpen_top _) le_top)
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (s2t_affineSpacePolynomialEquiv ι).bijective)
    hf

end HodgeLean.Foundations.Program
