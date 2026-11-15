import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedReesSection
import HodgeLean.Foundations.Program.SchoenTowerI2aCartierSpectrumNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerI2aCompatibleSpectrumNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerI2aReesOpenCoverage
import Mathlib.AlgebraicGeometry.Noetherian

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every actual paired Rees comparison to an integral locally Noetherian
retained blowup is an open immersion over the specified affine base.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13. -/
theorem s2v_i2a_retained_rees_open_immersion
    (Q : Scheme.{0}) (R : Type) [CommRing R] [IsDomain R]
    (π : Spec (CommRingCat.of R) ⟶ Q) (B : Over Q)
    [IsIntegral B.left] [IsLocallyNoetherian B.left]
    (b : B ⟶ Over.mk π) (K : (Spec (CommRingCat.of R)).IdealSheafData)
    (huniv : ∀ (Z : Over Q) (h : Z ⟶ Over.mk π),
      (∀ p : Z.left, ∃ U : Z.left.affineOpens, p ∈ U.1 ∧
        Nonempty (((K.comap h.left).ideal U) ≃ₗ[Γ(Z.left, U)] Γ(Z.left, U))) →
      ∃! v : Z ⟶ B, v ≫ b = h)
    (hcartier : ∀ p : B.left, ∃ U : B.left.affineOpens, p ∈ U.1 ∧
      Nonempty (((K.comap b.left).ideal U) ≃ₗ[Γ(B.left, U)] Γ(B.left, U)))
    (x y : R) (hx : x ≠ 0)
    (hK : K.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {x, y}).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    (g : Spec (CommRingCat.of (s2t_reesChart (Ideal.span {x, y}) x)) ⟶ B.left)
    (hg : g ≫ b.left = Spec.map (CommRingCat.ofHom (algebraMap R _))) :
    IsOpenImmersion g := by
  let C := s2t_reesChart (Ideal.span {x, y}) x
  letI : IsDomain (Localization.Away x) := Localization.Away.isDomain hx
  apply s2v_i2a_rees_open_immersion_of_sections R x y hx B.left b.left g hg
  intro q
  obtain ⟨S, hS, hSd, v, hv, hpv, hfree⟩ :=
    s2v_i2a_cartier_spectrum_neighborhood B.left (K.comap b.left) (g q) (hcartier (g q))
  letI : CommRing S := hS
  letI : IsDomain S := hSd
  letI : IsOpenImmersion v := hv
  obtain ⟨u, hu⟩ := Spec.map_surjective (v ≫ b.left)
  have hfreespec : Nonempty (((K.comap (Spec.map u)).ideal ⟨⊤, isAffineOpen_top _⟩)
      ≃ₗ[Γ(Spec (CommRingCat.of S), ⊤)] Γ(Spec (CommRingCat.of S), ⊤)) := by
    rw [hu, Scheme.IdealSheafData.comap_comp]
    exact hfree
  have he := s2v_i2a_spectrum_cartier_reflection R S u.hom (Ideal.span {x, y}) K hK hfreespec
  rw [Ideal.map_span, Set.image_pair] at he
  obtain ⟨e⟩ := he
  have hKv : (K.comap (v ≫ b.left)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {u.hom x, u.hom y}).map (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom := by
    rw [← hu, s2e_affine_comap_ideal, hK, Ideal.map_map]
    have hn : (Spec.map u).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp u.hom :=
      congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality u).symm
    rw [hn, ← Ideal.map_map, Ideal.map_span, Set.image_pair]
  obtain ⟨T, hT, hTd, w, φ, hw, hqw, hfactor⟩ :=
    s2v_i2a_compatible_spectrum_neighborhood g S v q hpv
  letI : CommRing T := hT
  letI : IsDomain T := hTd
  letI : IsOpenImmersion w := hw
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective w
  have hcoeff : φ.comp u.hom = ρ.hom.comp (algebraMap R C) := by
    have H : CommRingCat.ofHom (φ.comp u.hom) =
        CommRingCat.ofHom (ρ.hom.comp (algebraMap R C)) := by
      apply Spec.map_injective
      simp only [CommRingCat.ofHom_comp, Spec.map_comp]
      change Spec.map (CommRingCat.ofHom φ) ≫ Spec.map u =
        Spec.map ρ ≫ Spec.map (CommRingCat.ofHom (algebraMap R C))
      rw [hu, ← Category.assoc, hfactor, Category.assoc, hg, hρ]
    exact congrArg CommRingCat.Hom.hom H
  have hρinj : Function.Injective ρ.hom := by
    have hd : DenseRange (PrimeSpectrum.comap ρ.hom) := by
      change DenseRange (Spec.map ρ)
      rw [hρ]
      exact w.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty w)
    apply (RingHom.injective_iff_ker_eq_bot ρ.hom).mpr
    apply le_bot_iff.mp
    simpa only [nilradical_eq_zero, Ideal.zero_eq_bot] using
      (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical ρ.hom).mp hd
  have hxC : algebraMap R C x ≠ 0 := by
    have hi : Function.Injective (algebraMap R (Localization.Away x)) :=
      IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
    intro H
    exact hx (hi ((congrArg Subtype.val H).trans (map_zero _).symm))
  have hxT : ρ.hom (algebraMap R C x) ≠ 0 :=
    fun H => hxC (hρinj (H.trans (map_zero _).symm))
  obtain ⟨s, hs, hsu, η, ψ, hη, hψ, hηψ, hsection, hsource⟩ :=
    s2v_i2a_retained_rees_section_on_cartier_neighborhood Q (Over.mk π) B b K huniv
      R S T u.hom x y e (𝟙 _) v (by simpa using hu.symm) hKv g
      (by simpa using hg) ρ.hom φ hcoeff hxT (by simpa [hρ] using hfactor)
  letI : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
  let j := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s))) ≫ v
  refine ⟨Spec (CommRingCat.of (Localization.Away s)), j,
    Spec.map (CommRingCat.ofHom ψ), inferInstance, inferInstance, inferInstance, hsection, ?_⟩
  obtain ⟨t, ht⟩ := hqw
  refine ⟨Spec.map (CommRingCat.ofHom η) t, ?_⟩
  have H := congrArg (fun f : Spec (CommRingCat.of T) ⟶ B.left => f t) hsource
  change j (Spec.map (CommRingCat.ofHom η) t) = g (Spec.map ρ t) at H
  simpa only [hρ, ht] using H

end HodgeLean.Foundations.Program
