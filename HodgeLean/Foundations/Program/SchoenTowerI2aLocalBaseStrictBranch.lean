import HodgeLean.Foundations.Program.SchoenTowerI2aEtaleStrictChart

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A single labeled branch retains its actual reduced strict ideal on a
commuting etale chart over an affine base neighborhood; the selected exceptional
branch has unit ideal and every other coordinate retains its principal ideal.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `Scheme.IdealSheafData.support_comap`. -/
theorem s2v_i2a_local_base_etale_strict_branch_ideal
    (A : Type) [CommRing A] [IsDomain A] (n : ℕ) (i j k : Fin n) (hij : i ≠ j)
    {U X Y V : Scheme.{0}} [IsAffine U] (u : U ⟶ X) [IsOpenImmersion u]
    (f : X ⟶ Y) (c : V ⟶ Y) (v : U ⟶ V) (hbase : u ≫ f = v ≫ c)
    (d : V ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) A)))
    (a : MvPolynomial (Fin n) A →+* Γ(U, ⊤)) (ha : a.Etale)
    (D K : Y.IdealSheafData)
    (hD : (D.comap c).support.carrier = d ⁻¹' PrimeSpectrum.zeroLocus {MvPolynomial.X k})
    (hK : (K.comap c).support.carrier = d ⁻¹'
      PrimeSpectrum.zeroLocus {MvPolynomial.X i, MvPolynomial.X j})
    (hsq : v ≫ d = (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom a)) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom MvPolynomial.C
        (fun l => if l = j then MvPolynomial.X i * MvPolynomial.X j else MvPolynomial.X l)))) :
    ((s2c_strictTransform f D K).comap u).ideal ⟨⊤, isAffineOpen_top U⟩ =
      if k = i then ⊤ else Ideal.span {a (MvPolynomial.X k)} := by
  classical
  letI := a.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) A) Γ(U, ⊤) := ha
  haveI : Etale (Spec.map (CommRingCat.ofHom a)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr ha
  let w := U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom a)
  haveI : Etale w := by dsimp [w]; infer_instance
  have hs : u ⁻¹' ((s2c_strictTransform f D K).support : Set X) =
      if k = i then ∅ else w ⁻¹' PrimeSpectrum.zeroLocus {MvPolynomial.X k} := by
    rw [s2e_strictTransform_support_on_open, hbase]
    have hD' : c ⁻¹' (D.support : Set Y) =
        d ⁻¹' PrimeSpectrum.zeroLocus {MvPolynomial.X k} := by
      change (D.support.preimage c.continuous).carrier = _
      simpa only [Scheme.IdealSheafData.support_comap] using hD
    have hK' : c ⁻¹' (K.support : Set Y) =
        d ⁻¹' PrimeSpectrum.zeroLocus {MvPolynomial.X i, MvPolynomial.X j} := by
      change (K.support.preimage c.continuous).carrier = _
      simpa only [Scheme.IdealSheafData.support_comap] using hK
    change closure (v ⁻¹' (c ⁻¹' (D.support : Set Y) \ c ⁻¹' (K.support : Set Y))) = _
    rw [hD', hK', ← Set.preimage_sdiff]
    change closure ((v ≫ d) ⁻¹' _) = _
    rw [hsq]
    change closure (w ⁻¹' (PrimeSpectrum.comap (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun l => if l = j then MvPolynomial.X i * MvPolynomial.X j else MvPolynomial.X l)) ⁻¹'
        (PrimeSpectrum.zeroLocus {MvPolynomial.X k} \
          PrimeSpectrum.zeroLocus {MvPolynomial.X i, MvPolynomial.X j}))) = _
    rw [← w.isOpenMap.preimage_closure_eq_closure_preimage w.continuous,
      s2v_i2a_paired_polynomial_strict_support i j hij k]
    split_ifs <;> rfl
  by_cases hki : k = i
  · rw [if_pos hki]
    apply s2v_i2a_strict_transform_ideal_on_open u f D K ⊤ (by intro _ _; trivial)
    rw [hs, if_pos hki]
    change ∅ = U.zeroLocus (U := ⊤) (Set.univ : Set Γ(U, ⊤))
    rw [Scheme.zeroLocus_univ]
    simp only [TopologicalSpace.Opens.coe_top, Set.compl_univ]
  · rw [if_neg hki]
    apply s2v_i2a_strict_transform_ideal_on_open u f D K _
      (s2v_i2a_etale_coordinate_radical A (Fin n) Γ(U, ⊤) k)
    rw [hs, if_neg hki, Scheme.zeroLocus_span]
    change U.toSpecΓ ⁻¹' (PrimeSpectrum.comap a ⁻¹' PrimeSpectrum.zeroLocus {MvPolynomial.X k}) = _
    rw [PrimeSpectrum.preimage_comap_zeroLocus, Set.image_singleton,
      U.toSpecΓ_preimage_zeroLocus]
    rfl

end HodgeLean.Foundations.Program
