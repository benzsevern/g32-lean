import HodgeLean.Foundations.Program.SchoenTowerI2aEtaleStrictSupport
import HodgeLean.Foundations.Program.SchoenTowerI2aEtaleReduced
import HodgeLean.Foundations.Program.SchoenTowerI2aStrictIdealIdentification

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A commuting actual etale paired chart identifies every reduced strict
branch ideal with its specified principal coordinate, including the unit ideal
for the branch removed from this chart.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `Scheme.IdealSheafData.vanishingIdeal_support`. -/
theorem s2v_i2a_actual_etale_strict_branch_ideals
    (A : Type) [CommRing A] [IsDomain A] (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    {U X Y : Scheme} [IsAffine U] (u : U ⟶ X) [IsOpenImmersion u] (f : X ⟶ Y)
    (c : Y ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) A)))
    (a : MvPolynomial (Fin n) A →+* Γ(U, ⊤)) (ha : a.Etale)
    (D : Fin n → Y.IdealSheafData) (K : Y.IdealSheafData)
    (hD : ∀ k, (D k).support.carrier = c ⁻¹' PrimeSpectrum.zeroLocus {MvPolynomial.X k})
    (hK : K.support.carrier = c ⁻¹'
      PrimeSpectrum.zeroLocus {MvPolynomial.X i, MvPolynomial.X j})
    (hsq : (u ≫ f) ≫ c = (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom a)) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom MvPolynomial.C
        (fun k => if k = j then MvPolynomial.X i * MvPolynomial.X j else MvPolynomial.X k)))) :
    ∀ k, ((s2c_strictTransform f (D k) K).comap u).ideal ⟨⊤, isAffineOpen_top U⟩ =
      if k = i then ⊤ else Ideal.span {a (MvPolynomial.X k)} := by
  classical
  letI := a.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) A) Γ(U, ⊤) := ha
  haveI : Etale (Spec.map (CommRingCat.ofHom a)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr ha
  let v := U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom a)
  haveI : Etale v := by dsimp [v]; infer_instance
  have hs := s2v_i2a_etale_paired_strict_branch_support A n i j hij u f c v D K hD hK hsq
  intro k
  by_cases hki : k = i
  · rw [if_pos hki]
    apply s2v_i2a_strict_transform_ideal_on_open u f (D k) K ⊤
      (by intro _ _; trivial)
    rw [hs k, if_pos hki]
    change ∅ = U.zeroLocus (U := ⊤) (Set.univ : Set Γ(U, ⊤))
    rw [Scheme.zeroLocus_univ]
    simp only [TopologicalSpace.Opens.coe_top, Set.compl_univ]
  · rw [if_neg hki]
    apply s2v_i2a_strict_transform_ideal_on_open u f (D k) K _
      (s2v_i2a_etale_coordinate_radical A (Fin n) Γ(U, ⊤) k)
    rw [hs k, if_neg hki, Scheme.zeroLocus_span]
    change U.toSpecΓ ⁻¹' (PrimeSpectrum.comap a ⁻¹' PrimeSpectrum.zeroLocus {MvPolynomial.X k}) = _
    rw [PrimeSpectrum.preimage_comap_zeroLocus, Set.image_singleton,
      U.toSpecΓ_preimage_zeroLocus]
    rfl

end HodgeLean.Foundations.Program
