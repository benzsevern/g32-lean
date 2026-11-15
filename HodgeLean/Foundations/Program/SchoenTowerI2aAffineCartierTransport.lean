import HodgeLean.Foundations.Program.SchoenTowerI2aReesCartierTest

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A free extended coefficient ideal gives the actual global Cartier module
on its spectrum, with the specified ideal sheaf and coefficient map retained.
Source: Mathlib, `Scheme.ΓSpecIso_inv_naturality`;
Hartshorne, Algebraic Geometry, II.5, affine quasi-coherent ideals. -/
theorem s2v_i2a_spectrum_cartier_transport
    (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Ideal R)
    (K : (Spec (CommRingCat.of R)).IdealSheafData)
    (hK : K.ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    (hfree : Nonempty ((I.map φ) ≃ₗ[S] S)) :
    Nonempty (((K.comap (Spec.map (CommRingCat.ofHom φ))).ideal
      ⟨⊤, isAffineOpen_top _⟩) ≃ₗ[Γ(Spec (CommRingCat.of S), ⊤)]
        Γ(Spec (CommRingCat.of S), ⊤)) := by
  rw [s2e_affine_comap_ideal, hK, Ideal.map_map]
  have hn : (Spec.map (CommRingCat.ofHom φ)).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp φ := by
    exact congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  rw [hn, ← Ideal.map_map]
  exact s2v_i2a_cartier_ideal_ring_equiv
    (Scheme.ΓSpecIso (CommRingCat.of S)).symm.commRingCatIsoToRingEquiv _ hfree

/-- The actual spectrum Cartier module recovers freeness of the extended
coefficient ideal through the canonical spectrum section isomorphism.
Source: Mathlib, `Scheme.ΓSpecIso_inv_naturality` and `Scheme.ΓSpecIso`. -/
theorem s2v_i2a_spectrum_cartier_reflection
    (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Ideal R)
    (K : (Spec (CommRingCat.of R)).IdealSheafData)
    (hK : K.ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    (hfree : Nonempty (((K.comap (Spec.map (CommRingCat.ofHom φ))).ideal
      ⟨⊤, isAffineOpen_top _⟩) ≃ₗ[Γ(Spec (CommRingCat.of S), ⊤)]
        Γ(Spec (CommRingCat.of S), ⊤))) : Nonempty ((I.map φ) ≃ₗ[S] S) := by
  rw [s2e_affine_comap_ideal, hK, Ideal.map_map] at hfree
  have hn : (Spec.map (CommRingCat.ofHom φ)).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp φ := by
    exact congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  rw [hn, ← Ideal.map_map] at hfree
  have H := s2v_i2a_cartier_ideal_ring_equiv
    (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv _ hfree
  change Nonempty ((((I.map φ).map (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom).map
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom) ≃ₗ[S] S) at H
  rw [Ideal.map_map] at H
  have he : (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom = RingHom.id S :=
    congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of S)).inv_hom_id
  rwa [he, Ideal.map_id] at H

end HodgeLean.Foundations.Program
