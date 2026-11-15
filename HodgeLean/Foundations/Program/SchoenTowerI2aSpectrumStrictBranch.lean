import HodgeLean.Foundations.Program.SchoenTowerI2aLocalBaseStrictBranch
import HodgeLean.Foundations.Program.SchoenTowerI2aSpectrumIdealSupport

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual affine coefficient equations and a paired etale substitution square
identify the reduced strict ideal of each specified branch on the source spectrum.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `toSpecΓ_SpecMap_ΓSpecIso_inv`. -/
theorem s2v_i2a_spectrum_etale_strict_branch_ideal
    (A : Type) [CommRing A] [IsDomain A] (n : ℕ) (i j k : Fin n) (hij : i ≠ j)
    (R C : Type) [CommRing R] [CommRing C]
    (d : MvPolynomial (Fin n) A →+* R) (a : MvPolynomial (Fin n) A →+* C) (ha : a.Etale)
    (φ : R →+* C)
    (hsq : φ.comp d = a.comp (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun l => if l = j then MvPolynomial.X i * MvPolynomial.X j else MvPolynomial.X l)))
    {X Y : Scheme.{0}} (f : X ⟶ Y) (c : Spec (CommRingCat.of R) ⟶ Y)
    (g : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion g]
    (hbase : g ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ c) (D K : Y.IdealSheafData)
    (hD : (D.comap c).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {d (MvPolynomial.X k)}).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    (hK : (K.comap c).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {d (MvPolynomial.X i), d (MvPolynomial.X j)}).map
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :
    ((s2c_strictTransform f D K).comap g).ideal ⟨⊤, isAffineOpen_top _⟩ =
      if k = i then ⊤ else Ideal.span {((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
        (a (MvPolynomial.X k)))} := by
  classical
  let aΓ := (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom.comp a
  have haΓ : aΓ.Etale := RingHom.Etale.stableUnderComposition _ _ ha
    (RingHom.Etale.of_bijective (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.bijective)
  have hv : (Spec (CommRingCat.of C)).toSpecΓ ≫ Spec.map (CommRingCat.ofHom aΓ) =
      Spec.map (CommRingCat.ofHom a) := by
    dsimp only [aΓ]
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc]
    change ((Spec (CommRingCat.of C)).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv) ≫ _ = _
    rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]
  apply s2v_i2a_local_base_etale_strict_branch_ideal A n i j k hij g f c
    (Spec.map (CommRingCat.ofHom φ)) hbase (Spec.map (CommRingCat.ofHom d)) aΓ haΓ D K
  · rw [s2v_i2a_spectrum_ideal_support R (D.comap c) _ hD, PrimeSpectrum.zeroLocus_span]
    change PrimeSpectrum.zeroLocus {d (MvPolynomial.X k)} =
      PrimeSpectrum.comap d ⁻¹' PrimeSpectrum.zeroLocus {MvPolynomial.X k}
    rw [PrimeSpectrum.preimage_comap_zeroLocus, Set.image_singleton]
  · rw [s2v_i2a_spectrum_ideal_support R (K.comap c) _ hK, PrimeSpectrum.zeroLocus_span]
    change PrimeSpectrum.zeroLocus {d (MvPolynomial.X i), d (MvPolynomial.X j)} =
      PrimeSpectrum.comap d ⁻¹' PrimeSpectrum.zeroLocus {MvPolynomial.X i, MvPolynomial.X j}
    rw [PrimeSpectrum.preimage_comap_zeroLocus, Set.image_pair]
  · rw [hv, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hsq,
      CommRingCat.ofHom_comp, Spec.map_comp]

end HodgeLean.Foundations.Program
