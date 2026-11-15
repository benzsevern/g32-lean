import Mathlib.AlgebraicGeometry.Morphisms.Etale
import HodgeLean.Foundations.Program.SchoenTowerL1aLocalCurveCoordinate

/-! # Etale restriction maps between actual affine opens

The identity morphism gives etale maps on sections of nested affine opens.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
/-- Restriction between actual affine opens is etale on their section rings.
Source: Hartshorne, Algebraic Geometry, III.10, open immersions are etale. -/
theorem s2v_l1a_affine_section_restriction_etale
    {X : Scheme} (U V : X.affineOpens) (h : V.1 ≤ U.1) :
    (X.presheaf.map (homOfLE h).op).hom.Etale := by
  have H := Scheme.Hom.etale_appLE (𝟙 X) U.2 V.2 (show V.1 ≤ (𝟙 X) ⁻¹ᵁ U.1 from h)
  simpa only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] using H

attribute [local instance] overSpecAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of sections over the complex base is an algebra homomorphism for the actual structure maps.
Source: Hartshorne, Algebraic Geometry, II.2, the structure sheaf on affine opens. -/
def s2v_l1a_sectionRestrictionAlgHom
    (Z : Over (Spec ↧ℂ)) (U V : Z.left.Opens) (h : V ≤ U) :
    Γ(Z.left, U) →ₐ[ℂ] Γ(Z.left, V) :=
  { (Z.left.presheaf.map (homOfLE h).op).hom with
    commutes' := by
      intro c
      change ((Z.hom.appLE ⊤ U (by simp) ≫
        Z.left.presheaf.map (homOfLE h).op).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) =
          (Z.hom.appLE ⊤ V (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)
      rw [Scheme.Hom.appLE_map] }

/-- Actual etale coordinates restrict to any smaller affine neighborhood of their specified point.
Source: Hartshorne, Algebraic Geometry, III.10, restriction and composition of etale morphisms. -/
def s2v_l1a_restrict_localEtaleCoordinates
    {Z : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d Z.hom] {x : Z.left}
    (D : LocalEtaleCoordinates Z d x) (V : Z.left.affineOpens)
    (h : V.1 ≤ D.neighborhood) (hx : x ∈ V.1) : LocalEtaleCoordinates Z d x where
  neighborhood := V.1
  isAffine := V.2
  mem := hx
  coordinateAlgHom := (s2v_l1a_sectionRestrictionAlgHom Z D.neighborhood V.1 h).comp
    D.coordinateAlgHom
  etale := s2v_l1a_etale_ringHom_comp _ _ D.etale
    (s2v_l1a_affine_section_restriction_etale ⟨D.neighborhood, D.isAffine⟩ V h)

end HodgeLean.Foundations.Program
