import HodgeLean.Foundations.Program.SchoenTowerL1aEtalePointSupport
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Simultaneous point equations on one principal neighborhood

Finite point equations use one localization retaining the whole support.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A principal ideal equation survives any further localization whose denominator
is divisible by the original denominator. -/
theorem s2v_l1b_point_equation_refine
    {A : Type} [CommRing A] (I : Ideal A) (g d e : A) (hde : d ∣ e)
    (h : I.map (algebraMap A (Localization.Away d)) =
      Ideal.span {algebraMap A (Localization.Away d) g}) :
    I.map (algebraMap A (Localization.Away e)) =
      Ideal.span {algebraMap A (Localization.Away e) g} := by
  let f : Localization.Away d →+* Localization.Away e :=
    IsLocalization.Away.lift d (IsLocalization.Away.isUnit_of_dvd e hde)
  have hf : f.comp (algebraMap A (Localization.Away d)) =
      algebraMap A (Localization.Away e) := by
    ext a
    exact IsLocalization.Away.lift_eq d
      (IsLocalization.Away.isUnit_of_dvd e hde) a
  have H := congrArg (Ideal.map f) h
  rw [Ideal.map_map, hf, Ideal.map_span, Set.image_singleton] at H
  simpa only [← RingHom.comp_apply, hf] using H

/-- Finitely many etale point equations hold in one localization retaining every
specified rational point, with exact kernel ideals for all selected equations. -/
theorem s2v_l1b_simultaneous_point_equations
    {K A ι κ : Type} [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] [Finite ι] [Fintype κ]
    (φ : ι → A →ₐ[K] K) (hinj : Function.Injective φ)
    (j : κ → ι) (g : κ → A)
    (hEt : ∀ k, (Polynomial.aeval (R := K) (g k)).toRingHom.Etale)
    (hg0 : ∀ k, φ (j k) (g k) = 0)
    (hg : ∀ k i, i ≠ j k → φ i (g k) ≠ 0) :
    ∃ d : A, (∀ i, φ i d = 1) ∧
      ∀ k, (RingHom.ker (φ (j k)).toRingHom).map
        (algebraMap A (Localization.Away d)) =
        Ideal.span {algebraMap A (Localization.Away d) (g k)} := by
  classical
  choose d hd hI using fun k =>
    s2v_l1a_etale_parameter_point_support φ hinj (j k) (g k) (hEt k) (hg0 k) (hg k)
  refine ⟨∏ k, d k, ?_, ?_⟩
  · intro i
    simp only [map_prod, hd, Finset.prod_const_one]
  · intro k
    exact s2v_l1b_point_equation_refine _ _ _ _
      (Finset.dvd_prod_of_mem d (Finset.mem_univ k)) (hI k)

/-- Subtracting a scalar from a univariate parameter preserves etaleness. -/
theorem s2v_l1b_univariate_translation_etale
    {K A : Type} [CommRing K] [CommRing A] [Algebra K A]
    (g : A) (c : K) (hEt : (Polynomial.aeval (R := K) g).toRingHom.Etale) :
    (Polynomial.aeval (R := K) (g - algebraMap K A c)).toRingHom.Etale := by
  let e := Polynomial.algEquivAevalXAddC (-c)
  have H := RingHom.Etale.stableUnderComposition e.toRingHom
    (Polynomial.aeval (R := K) g).toRingHom
    (RingHom.Etale.of_bijective e.bijective) hEt
  have heq : (Polynomial.aeval (R := K) g).comp e.toAlgHom =
      Polynomial.aeval (R := K) (g - algebraMap K A c) := by
    apply Polynomial.algHom_ext
    simp [e, Polynomial.algEquivAevalXAddC, sub_eq_add_neg]
  exact congrArg AlgHom.toRingHom heq ▸ H

/-- One separating etale parameter gives the exact ideals of all specified
rational points after one principal restriction retaining their entire support. -/
theorem s2v_l1b_separating_parameter_point_equations
    {K A ι : Type} [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] [Fintype ι]
    (φ : ι → A →ₐ[K] K) (hinj : Function.Injective φ) (g : A)
    (hEt : (Polynomial.aeval (R := K) g).toRingHom.Etale)
    (hsep : Function.Injective (fun i => φ i g)) :
    ∃ d : A, (∀ i, φ i d = 1) ∧
      ∀ i, (RingHom.ker (φ i).toRingHom).map
        (algebraMap A (Localization.Away d)) =
        Ideal.span {algebraMap A (Localization.Away d) (g - algebraMap K A (φ i g))} := by
  apply s2v_l1b_simultaneous_point_equations φ hinj id
    (fun i => g - algebraMap K A (φ i g))
  · intro i
    exact s2v_l1b_univariate_translation_etale g (φ i g) hEt
  · intro i
    simp only [map_sub, AlgHom.commutes, id_eq, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  · intro k i hik
    simp only [map_sub, AlgHom.commutes, id_eq, Algebra.algebraMap_self, RingHom.id_apply, sub_ne_zero]
    exact fun h => hik (hsep h)

end HodgeLean.Foundations.Program
