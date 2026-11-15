import HodgeLean.Foundations.Program.SchoenCycleC11AffineHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11StandardHelpers
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Affine etale inverse transport
Section-algebra coordinates transport relative root inverses to actual scheme points.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Affine coordinate homeomorphisms intertwine actual point maps with precomposition.
Source: ComplexPoint.affineSpecEquiv_affineSpecComplexPointMap and scheme isomorphism identities. -/
theorem s2e_c11_affineCoordinateHomeomorph_naturality_hi
    (X Y : Over (Spec ↧ℂ)) [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    (z : Point ℂ X) :
    letI := s2e_c11_affineSectionAlgebra X
    letI := s2e_c11_affineSectionAlgebra Y
    s2e_c11_affineCoordinateHomeomorph Y (Point.map f z) =
      (s2e_c11_affineCoordinateHomeomorph X z).comp (s2e_c11_affineCoordinateAlgHom X Y f) := by
  letI := s2e_c11_affineSectionAlgebra X
  letI := s2e_c11_affineSectionAlgebra Y
  let ex := s2e_c11_affineCoordinateIso X
  let ey := s2e_c11_affineCoordinateIso Y
  let g := s2e_c11_affineCoordinateAlgHom X Y f
  have hs : affineSpecComplexPointMap g (Point.map ex.hom z) =
      Point.map ey.hom (Point.map f z) := by
    apply Over.OverMorphism.ext
    change (z.left ≫ ex.hom.left) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
      (z.left ≫ f.left) ≫ ey.hom.left
    rw [s2e_c11_affineCoordinateAlgHom_spec]
    simp only [Category.assoc]
    have he : ex.hom.left ≫ ex.inv.left = 𝟙 X.left := by
      exact congrArg (fun a => a.left) ex.hom_inv_id
    rw [← Category.assoc ex.hom.left ex.inv.left, he, Category.id_comp]
  have h := affineSpecEquiv_affineSpecComplexPointMap g (Point.map ex.hom z)
  rw [hs] at h
  exact h

/-- Etale maps between affine complex schemes have analytic local inverses.
Source: Mathlib, etale affine comparison and standard-etale neighbourhoods. -/
theorem s2e_c11_affine_scheme_etale_local_inverse_hi
    (X Y : Over (Spec ↧ℂ)) [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) [Etale f.left] : IsLocalHomeomorph (Point.map f) := by
  letI := s2e_c11_affineSectionAlgebra X
  letI := s2e_c11_affineSectionAlgebra Y
  let A := Γ(Y.left, ⊤)
  let B := Γ(X.left, ⊤)
  let g : A →ₐ[ℂ] B := s2e_c11_affineCoordinateAlgHom X Y f
  letI : Algebra A B := g.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  have het : g.toRingHom.Etale := by
    have h : Etale (Spec.map (CommRingCat.ofHom g.toRingHom)) := by
      rw [s2e_c11_affineCoordinateAlgHom_spec]
      infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @Etale)] at h
    exact h
  letI : Algebra.Etale A B := RingHom.etale_algebraMap.mp het
  have hp : IsLocalHomeomorph (fun φ : B →ₐ[ℂ] ℂ => φ.comp g) :=
    s2e_c11_etaleAlgebra_local_inverse
  let ex := s2e_c11_affineCoordinateHomeomorph X
  let ey := s2e_c11_affineCoordinateHomeomorph Y
  have heq : Point.map f = ey.symm ∘ (fun φ : B →ₐ[ℂ] ℂ => φ.comp g) ∘ ex := by
    funext z
    apply ey.injective
    exact (s2e_c11_affineCoordinateHomeomorph_naturality_hi X Y f z).trans
      (ey.apply_symm_apply _).symm
  rw [heq]
  exact ey.symm.isLocalHomeomorph.comp (hp.comp ex.isLocalHomeomorph)

end HodgeLean.Foundations.Program
