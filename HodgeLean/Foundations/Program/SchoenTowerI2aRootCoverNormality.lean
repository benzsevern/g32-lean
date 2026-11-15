import Mathlib.Algebra.Field.ULift
import Mathlib.Analysis.Complex.Polynomial.Basic
import HodgeLean.Foundations.Mathlib.ZmtIso
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-! # Local normality and generic components of root covers
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
universe u

/-- Every prime localization of a smooth algebra over a field is a normal domain.
Source: AlgebraicGeometry.zmtiso_normal_of_smooth and AlgebraicGeometry.Spec.stalkIso. -/
theorem s2v_i2a_smooth_localization_normal
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]
    (p : Ideal A) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let s : Spec ↧A ⟶ Spec ↧k := Spec.map (CommRingCat.ofHom (algebraMap k A))
  letI : Smooth s := (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)
  have H := zmtiso_normal_of_smooth (Spec ↧A) s (⟨p, inferInstance⟩ : PrimeSpectrum A)
  letI := H.1
  let e := (AlgebraicGeometry.Spec.stalkIso (CommRingCat.of A)
    (⟨p, inferInstance⟩ : PrimeSpectrum A)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain, H.2.of_equiv e⟩

/-- Prime localizations of smooth complex algebras are normal domains in every ambient universe.
Source: AlgebraicGeometry.zmtiso_normal_of_smooth; Mathlib, Algebra.Smooth.comp and ULift.algebra'. -/
theorem s2v_i2a_complex_smooth_localization_normal
    (A : Type u) [CommRing A] [Algebra ℂ A] [Algebra.Smooth ℂ A]
    (p : Ideal A) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let K := ULift.{u} ℂ
  letI : Algebra K ℂ := ULift.algebra' ℂ ℂ
  letI : SMul K ℂ := (inferInstance : Algebra K ℂ).toSMul
  letI : Module K ℂ := Algebra.toModule (R := K) (A := ℂ)
  letI : Algebra K A := ((algebraMap ℂ A).comp ULift.ringEquiv.toRingHom).toAlgebra
  letI : SMul K A := (inferInstance : Algebra K A).toSMul
  letI : Module K A := Algebra.toModule (R := K) (A := A)
  haveI : IsScalarTower K ℂ A := IsScalarTower.of_algebraMap_eq' (R := K) (S := ℂ) (A := A) rfl
  letI : Algebra.Etale K ℂ := (RingHom.etale_algebraMap).mp
    (RingHom.Etale.of_bijective ULift.ringEquiv.bijective)
  letI : Algebra.Smooth K A := Algebra.Smooth.comp K ℂ A
  exact s2v_i2a_smooth_localization_normal K A p

/-- Every prime localization of an etale algebra over the root polynomial ring is a normal domain.
Source: Mathlib, Algebra.Smooth.of_equiv and Algebra.Smooth.comp; AlgebraicGeometry.zmtiso_normal_of_smooth. -/
theorem s2v_i2a_etale_root_localization_normal
    (n : ℕ) (A : Type u) [CommRing A]
    (b : ULift.{0} (MvPolynomial (Fin n) ℂ) →+* A) (hb : b.Etale)
    (p : Ideal A) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let B := ULift.{0} (MvPolynomial (Fin n) ℂ)
  letI : Algebra B A := b.toAlgebra
  letI : SMul B A := (inferInstance : Algebra B A).toSMul
  letI : Module B A := Algebra.toModule (R := B) (A := A)
  letI : Algebra ℂ A := (b.comp (algebraMap ℂ B)).toAlgebra
  haveI : IsScalarTower ℂ B A := IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := B) (A := A) rfl
  letI : Algebra.Etale B A := hb.toAlgebra
  letI : Algebra.Smooth ℂ B := Algebra.Smooth.of_equiv
    (ULift.algEquiv (R := ℂ) (A := MvPolynomial (Fin n) ℂ)).symm
  letI : Algebra.Smooth ℂ A := Algebra.Smooth.comp ℂ B A
  exact s2v_i2a_complex_smooth_localization_normal A p

/-- A field map on an integral cover selects a minimal prime when its restriction to the base is injective.
Source: Mathlib, Ideal.IsIntegral.mem_minimalPrimes_map_under and RingHom.comap_ker. -/
theorem s2v_i2a_integral_cover_kernel_minimal
    {R A L : Type*} [CommRing R] [CommRing A] [Field L]
    (i : R →+* A) (hi : i.IsIntegral) (τ : A →+* L)
    (hinj : Function.Injective (τ.comp i)) : IsMinimalPrime (RingHom.ker τ) := by
  letI := i.toAlgebra
  letI : Algebra.IsIntegral R A := algebraMap_isIntegral_iff.mp hi
  letI : (RingHom.ker τ).IsPrime := RingHom.ker_isPrime τ
  have hzero : (RingHom.ker τ).under R = ⊥ := by
    change (RingHom.ker τ).comap i = ⊥
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
  have H := Ideal.IsIntegral.mem_minimalPrimes_map_under (R := R) (RingHom.ker τ)
  rw [hzero, Ideal.map_bot] at H
  exact H

/-- A minimal-prime field map embeds a domain localization at every prime containing its kernel.
Source: Mathlib, IsLocalization.lift and IsLocalization.minimalPrimes_map. -/
theorem s2v_i2a_localized_component_embedding
    {A L S : Type*} [CommRing A] [Field L] [CommRing S] [IsDomain S]
    (q : Ideal A) [q.IsPrime] [Algebra A S] [IsLocalization.AtPrime S q]
    (τ : A →+* L) (hmin : IsMinimalPrime (RingHom.ker τ))
    (hq : RingHom.ker τ ≤ q) :
    ∃ σ : S →+* L, Function.Injective σ ∧ σ.comp (algebraMap A S) = τ := by
  have hunit : ∀ y : q.primeCompl, IsUnit (τ y) := by
    intro y
    apply isUnit_iff_ne_zero.mpr
    intro hy
    exact y.2 (hq hy)
  let σ : S →+* L := IsLocalization.lift hunit
  have hσ : σ.comp (algebraMap A S) = τ := IsLocalization.lift_comp hunit
  have hker : (RingHom.ker σ).under A = RingHom.ker τ := by
    rw [Ideal.under_def, RingHom.comap_ker, hσ]
  have H : RingHom.ker σ ∈ ((⊥ : Ideal A).map (algebraMap A S)).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map q.primeCompl S]
    change IsMinimalPrime ((RingHom.ker σ).under A)
    rw [hker]
    exact hmin
  rw [Ideal.map_bot] at H
  have hzero : RingHom.ker σ = ⊥ := le_antisymm
    (H.2 ⟨inferInstance, bot_le⟩ bot_le) bot_le
  exact ⟨σ, (RingHom.injective_iff_ker_eq_bot σ).mpr hzero, hσ⟩

end HodgeLean.Foundations.Program
