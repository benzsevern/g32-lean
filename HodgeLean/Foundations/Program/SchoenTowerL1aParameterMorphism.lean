import HodgeLean.Foundations.Program.SchoenTowerL1aMorphismParameters
import HodgeLean.Foundations.Program.SchoenTowerL1aUnivariateEtale

/-! # Morphisms from etale section parameters

Implication from polynomial etaleness of actual sections to the actual
etale affine-space morphism with those sections as coordinates.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- Actual base sections identify with complex coefficients in every structure map.
Source: Hartshorne, Algebraic Geometry, II.2, the structure morphism on sections. -/
theorem s2v_l1a_structure_section_coefficients (X : Over (Spec ↧ℂ)) :
    X.hom.appTop.hom = (algebraMap ℂ Γ(X.left, ⊤)).comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.toRingHom := by
  ext k
  change X.hom.appTop.hom k =
    X.hom.appLE ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom k))
  rw [Iso.hom_inv_id_apply]
  simp only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl, op_id,
    X.left.presheaf.map_id, Category.comp_id]

/-- Polynomial etale parameters give the actual etale affine-space morphism
whose pullback coordinates are those parameters.
Source: Hartshorne, Algebraic Geometry, II.2 and III.10, affine etale morphisms. -/
theorem s2v_l1a_parameter_morphism
    (X : Over (Spec ↧ℂ)) [IsAffine X.left] (ι : Type)
    (z : ι → Γ(X.left, ⊤))
    (hEt : (MvPolynomial.eval₂Hom X.hom.appTop.hom z).Etale) :
    ∃ f : X ⟶ Over.mk (complexAffineSpace ι ↘ Spec ↧ℂ),
      Etale f.left ∧
      (∀ i, f.left.appTop (AffineSpace.coord (Spec ↧ℂ) i) = z i) := by
  let f := (s2t_affineSpaceOverHomEquiv X ι).symm z
  have hz (i : ι) : f.left.appTop (AffineSpace.coord (Spec ↧ℂ) i) = z i :=
    s2t_affineSpaceOverHomEquiv_symm_coord X ι z i
  have hEtC : (MvPolynomial.eval₂Hom (algebraMap ℂ Γ(X.left, ⊤)) z).Etale := by
    rw [s2v_l1a_structure_section_coefficients] at hEt
    exact (s2v_l1a_etale_eval_change_coefficients_iff _ _ _).mp hEt
  let e := s2t_affineSpacePolynomialEquiv ι
  have H : (f.left.appTop.hom.comp e.toRingHom).Etale := by
    rw [← s2v_l1a_affineSpace_section_polynomial_map]
    have hcoords : (fun i => f.left.appTop
        ((s2t_affineSpacePolynomialEquiv ι) (MvPolynomial.X i))) = z := by
      funext i
      have hcoord : (s2t_affineSpacePolynomialEquiv ι) (MvPolynomial.X i) =
          AffineSpace.coord (Spec ↧ℂ) i := SpecIso_hom_appTop_X i
      rw [hcoord]
      exact hz i
    rw [hcoords]
    exact hEtC
  have H' := RingHom.Etale.respectsIso.2 _ e.symm.toRingEquiv H
  have heq : (f.left.appTop.hom.comp e.toRingHom).comp e.symm.toRingHom =
      f.left.appTop.hom := by
    ext s
    exact congrArg f.left.appTop.hom (e.apply_symm_apply s)
  rw [heq] at H'
  letI : IsAffine (Over.mk (complexAffineSpace ι ↘ Spec ↧ℂ)).left :=
    inferInstanceAs (IsAffine (complexAffineSpace ι))
  exact ⟨f, (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := f.left)).mpr H', hz⟩

end HodgeLean.Foundations.Program
