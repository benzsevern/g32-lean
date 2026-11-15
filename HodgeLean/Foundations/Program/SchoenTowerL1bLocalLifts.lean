import HodgeLean.Foundations.Program.SchoenTowerL1bInvertibleIdeal
import HodgeLean.Foundations.Program.SchoenTowerL1bChartOverlap
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace HodgeLean.Foundations.Program
open Polynomial

/-- An ideal trivialization expresses every ideal element using one regular generator. -/
theorem s2v_l1b_trivialization_generator {A : Type*} [CommRing A]
    (I : Ideal A) (e : I ≃ₗ[A] A) :
    IsRegular (e.symm 1).val ∧ ∀ a : I, a.val = e a * (e.symm 1).val := by
  have hmul (a : A) : a • e.symm 1 = e.symm a := by
    rw [← map_smul, smul_eq_mul, mul_one]
  constructor
  · apply (Commute.isRegular_iff (fun _ => Commute.all _ _)).mpr
    intro a b hab
    apply e.symm.injective
    calc
      e.symm a = a • e.symm 1 := (hmul a).symm
      _ = b • e.symm 1 := Subtype.ext (by simpa only [Submodule.coe_smul, smul_eq_mul, mul_comm] using hab)
      _ = e.symm b := hmul b
  · intro a
    have h := congrArg Subtype.val (hmul (e a))
    simpa only [LinearEquiv.symm_apply_apply, Submodule.coe_smul, smul_eq_mul] using h.symm

/-- Flat base change preserves the regular generator extracted from an ideal trivialization. -/
theorem s2v_l1b_trivialization_generator_flat {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] (I : Ideal A) (e : I ≃ₗ[A] A) :
    IsRegular (algebraMap A B (e.symm 1).val) := by
  have h := (s2v_l1b_trivialization_generator I e).1
  apply (Commute.isRegular_iff (fun _ => Commute.all _ _)).mpr
  have hsm : IsSMulRegular A (e.symm 1).val := h.left
  exact hsm.of_flat (S := B)

/-- Inverting a trivialization coefficient makes its ideal element regular after flat base change. -/
theorem s2v_l1b_trivialization_element_flat {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] (I : Ideal A) (e : I ≃ₗ[A] A)
    (v : I) (hv : IsUnit (algebraMap A B (e v))) :
    IsRegular (algebraMap A B v.val) := by
  rw [(s2v_l1b_trivialization_generator I e).2 v, map_mul]
  exact hv.isRegular.mul (s2v_l1b_trivialization_generator_flat I e)

/-- A unit coefficient gives a unique ratio on any flat algebra of a trivializing ring. -/
theorem s2v_l1b_trivialization_ratio_flat {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] (I : Ideal A) (e : I ≃ₗ[A] A)
    (u v : I) (hv : IsUnit (algebraMap A B (e v))) :
    ∃! s : B, algebraMap A B u.val = s * algebraMap A B v.val := by
  obtain ⟨w, hw⟩ := hv
  let s : B := algebraMap A B (e u) * ↑w⁻¹
  have hs : algebraMap A B u.val = s * algebraMap A B v.val := by
    rw [(s2v_l1b_trivialization_generator I e).2 u,
      (s2v_l1b_trivialization_generator I e).2 v, map_mul, map_mul, ← hw]
    dsimp [s]
    rw [mul_assoc, ← mul_assoc (↑w⁻¹ : B), Units.inv_mul, one_mul]
  refine ⟨s, hs, ?_⟩
  intro t ht
  exact (s2v_l1b_trivialization_element_flat I e v ⟨w, hw⟩).right (ht.symm.trans hs)

/-- A regular image of the chart denominator determines a chart map from its base restriction. -/
theorem s2v_l1b_chart_hom_ext_regular {R B : Type*} [CommRing R] [CommRing B]
    (u v : R) (f : R →+* B) (hv : IsRegular (f v))
    (φ ψ : s2v_L1bChart u v →+* B)
    (hφ : φ.comp ((Ideal.Quotient.mk (Ideal.span {C u - X * C v})).comp C) = f)
    (hψ : ψ.comp ((Ideal.Quotient.mk (Ideal.span {C u - X * C v})).comp C) = f) :
    φ = ψ := by
  let q := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
  have hφC (a : R) : φ (q (C a)) = f a := DFunLike.congr_fun hφ a
  have hψC (a : R) : ψ (q (C a)) = f a := DFunLike.congr_fun hψ a
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro a
    exact (hφC a).trans (hψC a).symm
  · change φ (q X) = ψ (q X)
    apply hv.right
    have h₁ := congrArg φ (s2v_l1b_chart_relation u v)
    have h₂ := congrArg ψ (s2v_l1b_chart_relation u v)
    rw [map_mul, hφC, hφC] at h₁
    rw [map_mul, hψC, hψC] at h₂
    exact h₁.symm.trans h₂

/-- A unit ideal coefficient supplies the unique chart map over the base after flat base change. -/
theorem s2v_l1b_chart_lift_flat {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] (u v : R) (f : R →+* A)
    (I : Ideal A) (hu : f u ∈ I) (hv : f v ∈ I) (e : I ≃ₗ[A] A)
    (hvunit : IsUnit (algebraMap A B (e ⟨f v, hv⟩))) :
    ∃! φ : s2v_L1bChart u v →+* B,
      φ.comp ((Ideal.Quotient.mk (Ideal.span {C u - X * C v})).comp C) =
        (algebraMap A B).comp f := by
  obtain ⟨s, hs, _⟩ := s2v_l1b_trivialization_ratio_flat I e ⟨f u, hu⟩ ⟨f v, hv⟩ hvunit
  obtain ⟨φ, hφ, _⟩ := s2v_l1b_chart_lift u v ((algebraMap A B).comp f) s hs
  have hbase : φ.comp ((Ideal.Quotient.mk (Ideal.span {C u - X * C v})).comp C) =
      (algebraMap A B).comp f := by
    apply RingHom.ext
    intro a
    exact (DFunLike.congr_fun hφ (C a)).trans (eval₂_C _ _)
  refine ⟨φ, hbase, ?_⟩
  intro ψ hψ
  exact s2v_l1b_chart_hom_ext_regular u v _
    (s2v_l1b_trivialization_element_flat I e ⟨f v, hv⟩ hvunit) ψ φ hψ hbase

/-- Coefficient basic opens give a cover equipped with the unique maps to the two affine charts. -/
theorem s2v_l1b_coefficient_local_chart_cover {R A : Type*} [CommRing R] [CommRing A]
    (u v : R) (f : R →+* A) (I : Ideal A)
    (hu : f u ∈ I) (hv : f v ∈ I) (hI : I = Ideal.span {f u, f v}) (e : I ≃ₗ[A] A) :
    PrimeSpectrum.basicOpen (e ⟨f u, hu⟩) ⊔ PrimeSpectrum.basicOpen (e ⟨f v, hv⟩) = ⊤ ∧
    (∃! φ : s2v_L1bChart u v →+* Localization.Away (e ⟨f v, hv⟩),
      φ.comp ((Ideal.Quotient.mk (Ideal.span {C u - X * C v})).comp C) =
        (algebraMap A (Localization.Away (e ⟨f v, hv⟩))).comp f) ∧
    (∃! ψ : s2v_L1bChart v u →+* Localization.Away (e ⟨f u, hu⟩),
      ψ.comp ((Ideal.Quotient.mk (Ideal.span {C v - X * C u})).comp C) =
        (algebraMap A (Localization.Away (e ⟨f u, hu⟩))).comp f) := by
  refine ⟨s2v_l1b_invertible_ideal_basicOpen_cover I (f u) (f v) hu hv hI e, ?_, ?_⟩
  · exact s2v_l1b_chart_lift_flat u v f I hu hv e
      (IsLocalization.Away.algebraMap_isUnit (e ⟨f v, hv⟩))
  · exact s2v_l1b_chart_lift_flat v u f I hv hu e
      (IsLocalization.Away.algebraMap_isUnit (e ⟨f u, hu⟩))

/-- With regular denominator, an overlap map is determined by its restriction to the base. -/
theorem s2v_l1b_overlap_hom_ext_regular {R B : Type*} [CommRing R] [CommRing B]
    (u v : R) (f : R →+* B) (hv : IsRegular (f v))
    (φ ψ : s2v_L1bOverlap u v →+* B)
    (hφ : ((φ.comp (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v))).comp
      (Ideal.Quotient.mk (Ideal.span {C u - X * C v}))).comp C = f)
    (hψ : ((ψ.comp (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v))).comp
      (Ideal.Quotient.mk (Ideal.span {C u - X * C v}))).comp C = f) : φ = ψ := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X))
  exact s2v_l1b_chart_hom_ext_regular u v f hv _ _ hφ hψ

/-- Inverting both ideal coefficients supplies the unique map from the reciprocal overlap. -/
theorem s2v_l1b_overlap_lift_flat {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] (u v : R) (f : R →+* A)
    (I : Ideal A) (hu : f u ∈ I) (hv : f v ∈ I) (e : I ≃ₗ[A] A)
    (huunit : IsUnit (algebraMap A B (e ⟨f u, hu⟩)))
    (hvunit : IsUnit (algebraMap A B (e ⟨f v, hv⟩))) :
    ∃! φ : s2v_L1bOverlap u v →+* B,
      ((φ.comp (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v))).comp
        (Ideal.Quotient.mk (Ideal.span {C u - X * C v}))).comp C =
          (algebraMap A B).comp f := by
  obtain ⟨s, hs, _⟩ := s2v_l1b_trivialization_ratio_flat I e ⟨f u, hu⟩ ⟨f v, hv⟩ hvunit
  obtain ⟨t, ht, _⟩ := s2v_l1b_trivialization_ratio_flat I e ⟨f v, hv⟩ ⟨f u, hu⟩ huunit
  have hreg := s2v_l1b_trivialization_element_flat I e ⟨f v, hv⟩ hvunit
  have hst : s * t = 1 := by
    apply hreg.right
    change (s * t) * algebraMap A B (f v) = 1 * algebraMap A B (f v)
    rw [mul_comm s t, mul_assoc, ← hs, ← ht, one_mul]
  obtain ⟨φ, hφ, _⟩ := s2v_l1b_overlap_lift u v ((algebraMap A B).comp f) s hs
    (IsUnit.of_mul_eq_one t hst)
  have hbase : ((φ.comp (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v))).comp
      (Ideal.Quotient.mk (Ideal.span {C u - X * C v}))).comp C =
        (algebraMap A B).comp f := by
    apply RingHom.ext
    intro a
    exact (DFunLike.congr_fun hφ (C a)).trans (eval₂_C _ _)
  refine ⟨φ, hbase, ?_⟩
  intro ψ hψ
  exact s2v_l1b_overlap_hom_ext_regular u v _ hreg ψ φ hψ hbase

/-- The two overlap lifts agree through every reciprocal transition fixing the base sections. -/
theorem s2v_l1b_overlap_lifts_compatible {R B : Type*} [CommRing R] [CommRing B]
    (u v : R) (f : R →+* B) (hv : IsRegular (f v))
    (τ : s2v_L1bOverlap u v →+* s2v_L1bOverlap v u)
    (hτ : ∀ a : R, τ (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)
      (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) (C a))) =
      algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u)
        (Ideal.Quotient.mk (Ideal.span {C v - X * C u}) (C a)))
    (φ : s2v_L1bOverlap u v →+* B) (ψ : s2v_L1bOverlap v u →+* B)
    (hφ : ((φ.comp (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v))).comp
      (Ideal.Quotient.mk (Ideal.span {C u - X * C v}))).comp C = f)
    (hψ : ((ψ.comp (algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u))).comp
      (Ideal.Quotient.mk (Ideal.span {C v - X * C u}))).comp C = f) : ψ.comp τ = φ := by
  apply s2v_l1b_overlap_hom_ext_regular u v f hv _ φ _ hφ
  apply RingHom.ext
  intro a
  change ψ (τ _) = f a
  rw [hτ]
  exact DFunLike.congr_fun hψ a

end HodgeLean.Foundations.Program
