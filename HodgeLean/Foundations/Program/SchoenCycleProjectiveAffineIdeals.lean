import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartMaps

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- Restriction to an open subscheme preserves the reduced vanishing ideal.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; affine restriction of reduced ideals. -/
theorem s2e_open_comap_vanishingIdeal {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    (Z : TopologicalSpace.Closeds Y) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap f =
      Scheme.IdealSheafData.vanishingIdeal (Z.preimage f.continuous) := by
  have hrad : ((Scheme.IdealSheafData.vanishingIdeal Z).comap f).radical =
      (Scheme.IdealSheafData.vanishingIdeal Z).comap f := by
    ext U
    rw [Scheme.IdealSheafData.radical_ideal,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.vanishingIdeal_ideal, ← Ideal.comap_radical,
      (PrimeSpectrum.isRadical_vanishingIdeal _).radical]
  rw [← hrad, ← Scheme.IdealSheafData.vanishingIdeal_support,
    Scheme.IdealSheafData.support_comap]
  congr 1


/-- A reduced principal equation on an affine scheme has its principal vanishing ideal.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; affine vanishing ideals. -/
theorem s2e_spec_principal_vanishingIdeal (R : CommRingCat.{0}) (f : R)
    (hf : (Ideal.span {f}).IsRadical) :
    Ideal.map (Scheme.ΓSpecIso R).hom.hom
      ((Scheme.IdealSheafData.vanishingIdeal
        ⟨(PrimeSpectrum.basicOpen f).carrierᶜ, (PrimeSpectrum.basicOpen f).isOpen.isClosed_compl⟩).ideal
          ⟨⊤, isAffineOpen_top _⟩) = Ideal.span {f} := by
  let J : Ideal Γ(Spec R, ⊤) := (Ideal.span {f}).comap (Scheme.ΓSpecIso R).hom.hom
  let K := Scheme.IdealSheafData.ofIdealTop J
  have hJ : J.IsRadical := hf.comap _
  have hmap : (Spec R).presheaf.map (𝟙 (Opposite.op (⊤ : (Spec R).Opens))) = 𝟙 _ :=
    (Spec R).presheaf.map_id _
  have hrad : K.radical = K := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp only [K, Scheme.IdealSheafData.radical_ideal,
      Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id, hmap, Functor.map_id,
      CommRingCat.hom_id, Ideal.map_id]
    exact hJ.radical
  have hs : K.support =
      ⟨(PrimeSpectrum.basicOpen f).carrierᶜ, (PrimeSpectrum.basicOpen f).isOpen.isClosed_compl⟩ := by
    apply TopologicalSpace.Closeds.ext
    rw [Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus]
    have heq : (Scheme.ΓSpecIso R).inv ⁻¹' (J : Set Γ(Spec R, ⊤)) =
        (Ideal.span {f} : Set R) := by
      ext r
      change (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom r) ∈ Ideal.span {f} ↔ _
      simp only [← CommRingCat.hom_comp, ← RingHom.comp_apply, Iso.inv_hom_id,
        CommRingCat.hom_id, RingHom.id_apply]
      rfl
    rw [heq, PrimeSpectrum.zeroLocus_span]
    change PrimeSpectrum.zeroLocus ({f} : Set R) = (PrimeSpectrum.basicOpen f).carrierᶜ
    ext p
    simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, Set.mem_compl_iff,
      PrimeSpectrum.mem_basicOpen, not_not]
    change f ∈ p.asIdeal ↔ ¬ (f ∉ p.asIdeal)
    exact not_not.symm
  have hv : Scheme.IdealSheafData.vanishingIdeal K.support = K :=
    Scheme.IdealSheafData.vanishingIdeal_support.trans hrad
  rw [hs] at hv
  rw [hv]
  simp only [K, Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id, hmap,
    Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  exact Ideal.map_comap_of_surjective _ (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.surjective _


/-- An affine ring map pulls back a principal basic open by evaluation of its equation.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; standard affine chart maps. -/
theorem s2e_specMap_preimage_basicOpen {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) :
    Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ PrimeSpectrum.basicOpen r =
      PrimeSpectrum.basicOpen (f r) := by
  rw [SpecMap_preimage_basicOpen]
  rfl

end HodgeLean.Foundations.Program
