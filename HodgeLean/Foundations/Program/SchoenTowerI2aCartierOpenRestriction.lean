import HodgeLean.Foundations.Program.SchoenTowerI2aCartierInjectiveTransport
import HodgeLean.Foundations.Program.SchoenTowerI2aCartierOpenImage
import HodgeLean.Foundations.Program.SchoenTowerI2aCartierSpectrumNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerI2aCompatibleSpectrumNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerI2aAffineCartierTransport

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual pointwise Cartier test persists on every integral open source,
with the pulled-back ideal sheaf and its affine ideal modules retained.
Source: Hartshorne, Algebraic Geometry, II.6, locality of effective Cartier divisors;
Mathlib, `Scheme.IdealSheafData.comap_comp`. -/
theorem s2v_i2a_cartier_test_open_restriction
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (g : X ⟶ Y) [IsOpenImmersion g] (K : Y.IdealSheafData)
    (hcartier : ∀ p : Y, ∃ U : Y.affineOpens, p ∈ U.1 ∧
      Nonempty ((K.ideal U) ≃ₗ[Γ(Y, U)] Γ(Y, U))) :
    ∀ q : X, ∃ U : X.affineOpens, q ∈ U.1 ∧
      Nonempty (((K.comap g).ideal U) ≃ₗ[Γ(X, U)] Γ(X, U)) := by
  intro q
  obtain ⟨S, hS, hSd, v, hv, hqv, hfree⟩ :=
    s2v_i2a_cartier_spectrum_neighborhood Y K (g q) (hcartier (g q))
  letI : CommRing S := hS
  letI : IsDomain S := hSd
  letI : IsOpenImmersion v := hv
  obtain ⟨T, hT, hTd, w, φ, hw, hqw, hfactor⟩ :=
    s2v_i2a_compatible_spectrum_neighborhood g S v q hqv
  letI : CommRing T := hT
  letI : IsDomain T := hTd
  letI : IsOpenImmersion w := hw
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ) ≫ v) :=
    hfactor.symm ▸ inferInstance
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsOpenImmersion.of_comp _ v
  have hφ : Function.Injective φ := by
    have hd : DenseRange (PrimeSpectrum.comap φ) :=
      (Spec.map (CommRingCat.ofHom φ)).isOpenEmbedding.isOpen_range.dense
        (Set.range_nonempty _)
    apply (RingHom.injective_iff_ker_eq_bot φ).mpr
    apply le_bot_iff.mp
    simpa only [nilradical_eq_zero, Ideal.zero_eq_bot] using
      (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mp hd
  let I : Ideal S := ((K.comap v).ideal ⟨⊤, isAffineOpen_top _⟩).map
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
  have hI : Nonempty (I ≃ₗ[S] S) := s2v_i2a_cartier_ideal_ring_equiv
    (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv _ hfree
  have hKI : (K.comap v).ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom := by
    dsimp only [I]
    rw [Ideal.map_map]
    have he : (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom = RingHom.id _ :=
      congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id
    rw [he, Ideal.map_id]
  have hfreeT := s2v_i2a_spectrum_cartier_transport S T φ I (K.comap v) hKI
    (s2v_i2a_cartier_ideal_injective_transport φ hφ I hI)
  have hfreeW : Nonempty ((((K.comap g).comap w).ideal ⟨⊤, isAffineOpen_top _⟩)
      ≃ₗ[Γ(Spec (CommRingCat.of T), ⊤)] Γ(Spec (CommRingCat.of T), ⊤)) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← hfactor, Scheme.IdealSheafData.comap_comp]
    exact hfreeT
  refine ⟨⟨w ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion w⟩, ?_,
    s2v_i2a_cartier_free_on_open_image w (K.comap g) hfreeW⟩
  change q ∈ w ''ᵁ (⊤ : (Spec (CommRingCat.of T)).Opens)
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact hqw

end HodgeLean.Foundations.Program
