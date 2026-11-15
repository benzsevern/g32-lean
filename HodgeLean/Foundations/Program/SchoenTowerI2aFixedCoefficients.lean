import HodgeLean.Foundations.Program.SchoenTowerI2aFieldCoefficientFactorization
import HodgeLean.Foundations.Program.SchoenTowerI2aNormalizationCharts
import HodgeLean.Foundations.Program.SchoenCycleStep1Descent
import Mathlib.RingTheory.Localization.Integral

/-! # Affine coefficients of an identified field normalization
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
universe u

/-- An identified actual field normalization has no additional integral affine coefficients.
Source: Mathlib, normalizationObjIso and AlgEquiv.mapIntegralClosure. -/
theorem s2v_i2a_field_normalization_integral_coefficients
    {K : Type*} [Field K] {Y : Scheme}
    (θ : Spec (CommRingCat.of K) ⟶ Y) [QuasiCompact θ] [QuasiSeparated θ]
    [IsIso θ.fromNormalization] (U : Y.Opens) (hU : IsAffineOpen U)
    (hpre : θ ⁻¹ᵁ U = ⊤) :
    let eS : Γ(Spec (CommRingCat.of K), θ ⁻¹ᵁ U) ≅ CommRingCat.of K :=
      (Spec (CommRingCat.of K)).presheaf.mapIso (eqToIso hpre.symm).op ≪≫
        Scheme.ΓSpecIso (CommRingCat.of K)
    let φ : Γ(Y, U) →+* K := (θ.app U ≫ eS.hom).hom
    letI := φ.toAlgebra
    Function.Surjective (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) K)) := by
  intro eS φ
  letI := φ.toAlgebra
  letI := (θ.app U).hom.toAlgebra
  let E : Γ(Spec (CommRingCat.of K), θ ⁻¹ᵁ U) ≃ₐ[Γ(Y, U)] K :=
    { eS.commRingCatIsoToRingEquiv with commutes' r := rfl }
  let EI := E.mapIntegralClosure
  intro b
  obtain ⟨c, hc⟩ := s2e_step1_normalization_algebraMap_surjective
    (Spec (CommRingCat.of K)) Y θ U hU (EI.symm b)
  refine ⟨c, ?_⟩
  calc
    algebraMap Γ(Y, U) (integralClosure Γ(Y, U) K) c =
        EI (algebraMap Γ(Y, U)
          (integralClosure Γ(Y, U) Γ(Spec (CommRingCat.of K), θ ⁻¹ᵁ U)) c) :=
      (EI.commutes c).symm
    _ = b := by rw [hc, EI.apply_symm_apply]

/-- An algebraic field with no additional integral elements is the fraction field of its embedded coefficient ring.
Source: Mathlib, IsAlgebraic.exists_integral_multiple and IsFractionRing.of_field. -/
theorem s2v_i2a_fraction_field_of_integral_coefficients
    {R L : Type*} [CommRing R] [IsDomain R] [Field L] [Algebra R L]
    [Algebra.IsAlgebraic R L] (hinj : Function.Injective (algebraMap R L))
    (hsurj : Function.Surjective (algebraMap R (integralClosure R L))) :
    IsFractionRing R L := by
  letI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr hinj
  apply IsFractionRing.of_field
  intro z
  obtain ⟨s, hs, hint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) z).exists_integral_multiple
  obtain ⟨a, ha⟩ := hsurj ⟨s • z, hint⟩
  have H : algebraMap R L a = algebraMap R L s * z := by
    simpa only [Algebra.smul_def, Subalgebra.coe_algebraMap] using congrArg Subtype.val ha
  have hsmap : algebraMap R L s ≠ 0 := fun hz => hs (hinj (hz.trans (map_zero _).symm))
  refine ⟨a, s, ?_⟩
  apply (eq_div_iff hsmap).mpr
  rw [mul_comm]
  exact H.symm

/-- An actual intermediate field point whose normalization is the affine base has precisely the coefficient fraction field.
Source: Mathlib, algebraicity of finite field-point factors and normalizationObjIso. -/
theorem s2v_i2a_affine_normalization_fraction_field
    {K L : Type u} [Field K] [Field L] {U : Scheme}
    [IsAffine U] [IsReduced U]
    (κ : L →+* K) (η : Spec (CommRingCat.of K) ⟶ U)
    [IsDominant η] [LocallyQuasiFinite η]
    (θ : Spec (CommRingCat.of L) ⟶ U) [QuasiCompact θ] [QuasiSeparated θ]
    [IsIso θ.fromNormalization]
    (h : Spec.map (CommRingCat.ofHom κ) ≫ θ = η) :
    let φL : Γ(U, ⊤) →+* L := (θ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom).hom
    letI := φL.toAlgebra
    IsFractionRing Γ(U, ⊤) L := by
  intro φL
  letI : Algebra Γ(U, ⊤) L := φL.toAlgebra
  haveI : IsDominant (Spec.map (CommRingCat.ofHom κ) ≫ θ) := by rw [h]; infer_instance
  haveI : IsDominant θ := IsDominant.of_comp (Spec.map (CommRingCat.ofHom κ)) θ
  have hinj := s2v_i2a_field_point_coefficient_injective θ
  haveI : FaithfulSMul Γ(U, ⊤) L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsDomain Γ(U, ⊤) := IsDomain.of_faithfulSMul _ L
  haveI : Algebra.IsAlgebraic Γ(U, ⊤) L :=
    s2v_i2a_intermediate_field_point_algebraic κ η θ h
  have hsurj : Function.Surjective (algebraMap Γ(U, ⊤) (integralClosure Γ(U, ⊤) L)) := by
    have H := s2v_i2a_field_normalization_integral_coefficients θ ⊤ (isAffineOpen_top U)
      (show θ ⁻¹ᵁ ⊤ = ⊤ from rfl)
    simpa using H
  exact s2v_i2a_fraction_field_of_integral_coefficients hinj hsurj

end HodgeLean.Foundations.Program
