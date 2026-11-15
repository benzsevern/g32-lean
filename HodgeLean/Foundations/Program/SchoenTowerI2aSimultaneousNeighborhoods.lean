import HodgeLean.Foundations.Program.SchoenTowerL1aEtalePointSupport
import HodgeLean.Foundations.Program.SchoenTowerI2aShiftedParameters
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Simultaneous principal equations near finite support
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Finitely many principal ideal equations hold on one principal neighborhood retaining the entire specified support.
Source: Mathlib, IsLocalization.Away.lift, Ideal.map_map and localization at a product. -/
theorem s2v_i2a_common_principal_neighborhood
    {A K ι κ : Type*} [CommRing A] [CommRing K] [Fintype ι]
    (φ : κ → A →+* K) (d g : ι → A) (I : ι → Ideal A)
    (hd : ∀ k i, φ k (d i) = 1)
    (hI : ∀ i, (I i).map (algebraMap A (Localization.Away (d i))) =
      Ideal.span {algebraMap A (Localization.Away (d i)) (g i)}) :
    ∃ D : A, (∀ k, φ k D = 1) ∧
      ∀ i, (I i).map (algebraMap A (Localization.Away D)) =
        Ideal.span {algebraMap A (Localization.Away D) (g i)} := by
  classical
  let D := ∏ i, d i
  let L := Localization.Away D
  have hunitD : IsUnit (algebraMap A L D) :=
    IsLocalization.map_units L ⟨D, Submonoid.mem_powers D⟩
  have hunit (i : ι) : IsUnit (algebraMap A L (d i)) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap A L) (Finset.dvd_prod_of_mem d (Finset.mem_univ i))) hunitD
  refine ⟨D, ?_, ?_⟩
  · intro k
    simp only [D, map_prod, hd, Finset.prod_const_one]
  · intro i
    let f : Localization.Away (d i) →+* L := IsLocalization.Away.lift (d i) (hunit i)
    have hf : f.comp (algebraMap A (Localization.Away (d i))) = algebraMap A L :=
      IsLocalization.Away.lift_comp (d i) (hunit i)
    have H := congrArg (Ideal.map f) (hI i)
    rw [Ideal.map_map, hf, Ideal.map_span, Set.image_singleton] at H
    have hfg : f (algebraMap A (Localization.Away (d i)) (g i)) = algebraMap A L (g i) :=
      RingHom.congr_fun hf (g i)
    rw [hfg] at H
    exact H

/-- One localization realizes every specified point kernel by its shifted etale parameter, while retaining all points.
Source: Mathlib, etale point ideals and localization at a product of finite-support denominators. -/
theorem s2v_i2a_simultaneous_point_parameter_equations
    {K A ι : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    [Fintype ι] (φ : ι → A →ₐ[K] K) (hinj : Function.Injective φ)
    (z : A) (hz : (Polynomial.aeval (R := K) z).toRingHom.Etale)
    (hsep : Function.Injective (fun i => φ i z)) :
    ∃ D : A, (∀ i, φ i D = 1) ∧
      ∀ i, (RingHom.ker (φ i).toRingHom).map (algebraMap A (Localization.Away D)) =
        Ideal.span {algebraMap A (Localization.Away D) (z - algebraMap K A (φ i z))} := by
  classical
  have hpoint (i : ι) := s2v_l1a_etale_parameter_point_support φ hinj i
    (z - algebraMap K A (φ i z)) (s2v_i2a_shifted_parameter_etale z hz (φ i z))
    (by simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]) (by
      intro k hki hzero
      apply hki
      apply hsep
      exact sub_eq_zero.mp (by simpa only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using hzero))
  choose d hd hI using hpoint
  exact s2v_i2a_common_principal_neighborhood (fun i => (φ i).toRingHom) d
    (fun i => z - algebraMap K A (φ i z)) (fun i => RingHom.ker (φ i).toRingHom)
    (fun k i => hd i k) hI

end HodgeLean.Foundations.Program
