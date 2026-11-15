import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

noncomputable section
open scoped Classical
open IsLocalRing
namespace AlgebraicGeometry.SingularCycles

set_option backward.isDefEq.respectTransparency false in
theorem boundary_finite_fiber_free
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : PrimeSpectrum R)
    (h : ∀ (Q : Ideal S) [Q.IsPrime], (Q.comap (algebraMap R S)) = p.asIdeal →
      (Localization.localRingHom (Q.comap (algebraMap R S)) Q
        (algebraMap R S) rfl).Flat) :
    p ∈ Module.freeLocus R S := by
  let Rp := Localization.AtPrime p.asIdeal
  let B := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  have : Algebra.IsIntegral Rp B := ⟨isIntegral_localization⟩
  have hflat : Module.Flat Rp B := by
    apply Module.flat_of_isLocalized_maximal B B
      (fun Q _ => Localization.AtPrime Q) (fun Q _ => Algebra.linearMap B _)
    intro P hP
    let Q : Ideal S := P.comap (algebraMap S B)
    have hQ : Q.comap (algebraMap R S) = p.asIdeal := by
      change (P.under S).under R = p.asIdeal
      rw [Ideal.under_under, ← Ideal.under_under (A := R) (B := Rp)]
      have hm : P.under Rp = maximalIdeal Rp :=
        IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal P)
      rw [hm]
      exact Localization.AtPrime.under_maximalIdeal
    have : Q.IsPrime := Ideal.IsPrime.comap _
    have hf := h Q hQ
    let f := Localization.localRingHom (Q.comap (algebraMap R S)) Q
      (algebraMap R S) rfl
    letI : Algebra (Localization.AtPrime (Q.comap (algebraMap R S)))
        (Localization.AtPrime Q) := f.toAlgebra
    haveI : IsScalarTower R (Localization.AtPrime (Q.comap (algebraMap R S)))
        (Localization.AtPrime Q) :=
      .of_algebraMap_eq fun x => (Localization.localRingHom_to_map _ _ _ rfl x).symm
    haveI : Module.Flat (Localization.AtPrime (Q.comap (algebraMap R S)))
        (Localization.AtPrime Q) := hf
    haveI : Module.Flat R (Localization.AtPrime Q) :=
      Module.Flat.trans R (Localization.AtPrime (Q.comap (algebraMap R S))) _
    let e : Localization.AtPrime Q ≃ₐ[S] Localization.AtPrime P :=
      IsLocalization.algEquiv Q.primeCompl _ _
    haveI : Module.Flat R (Localization.AtPrime P) :=
      Module.Flat.of_linearEquiv (e.toLinearEquiv.restrictScalars R).symm
    exact (Module.flat_iff_of_isLocalization Rp p.asIdeal.primeCompl
      (Localization.AtPrime P)).mpr inferInstance
  letI := hflat
  haveI : Module.Finite Rp B := Module.Finite.of_isLocalizedModule
    p.asIdeal.primeCompl (IsScalarTower.toAlgHom R S B).toLinearMap
  haveI : Module.Free Rp B := Module.free_of_flat_of_isLocalRing
  exact (Module.mem_freeLocus_of_isLocalization p Rp B
    (IsScalarTower.toAlgHom R S B).toLinearMap).mpr inferInstance

set_option backward.isDefEq.respectTransparency false in
theorem boundary_free_fiber_flat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (hp : p ∈ Module.freeLocus R S)
    (Q : Ideal S) [Q.IsPrime] (hQ : Q.comap (algebraMap R S) = p.asIdeal) :
    (Localization.localRingHom (Q.comap (algebraMap R S)) Q
      (algebraMap R S) rfl).Flat := by
  let Rp := Localization.AtPrime p.asIdeal
  let B := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let A := Localization.AtPrime Q
  have hle : Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl ≤ Q.primeCompl := by
    rintro _ ⟨r, hr, rfl⟩ h
    exact hr (hQ ▸ h)
  letI : Algebra B A := IsLocalization.localizationAlgebraOfSubmonoidLe B A _ _ hle
  letI : IsScalarTower S B A :=
    IsLocalization.localization_isScalarTower_of_submonoid_le B A _ _ hle
  haveI : IsScalarTower R B A := IsScalarTower.to₁₃₄ R S B A
  haveI : IsLocalization (Q.primeCompl.map (algebraMap S B)) A :=
    IsLocalization.isLocalization_of_submonoid_le B A _ _ hle
  haveI : Module.Free Rp B := (Module.mem_freeLocus_of_isLocalization p Rp B
    (IsScalarTower.toAlgHom R S B).toLinearMap).mp hp
  haveI : Module.Flat R B := Module.Flat.trans R Rp B
  haveI : Module.Flat B A := IsLocalization.flat A (Q.primeCompl.map (algebraMap S B))
  haveI : Module.Flat R A := Module.Flat.trans R B A
  let f := Localization.localRingHom (Q.comap (algebraMap R S)) Q
    (algebraMap R S) rfl
  letI : Algebra (Localization.AtPrime (Q.comap (algebraMap R S))) A := f.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime (Q.comap (algebraMap R S))) A :=
    .of_algebraMap_eq fun x => (Localization.localRingHom_to_map _ _ _ rfl x).symm
  exact (Module.flat_iff_of_isLocalization
    (Localization.AtPrime (Q.comap (algebraMap R S)))
    (Q.comap (algebraMap R S)).primeCompl A).mpr inferInstance

end AlgebraicGeometry.SingularCycles
