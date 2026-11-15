import HodgeLean.Foundations.Program.SchoenCycleCurveJets
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Polynomial coordinates for finite parameter neighbourhoods -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
open Polynomial
namespace HodgeLean.Foundations.Program

/-- A polynomial vanishes to order at least `N` in a regular parameter exactly
when it is divisible by the `N`th power of the polynomial coordinate.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
uniqueness of parameter expansions. -/
theorem s2e_parameter_polynomial_vanishing_iff
    (R : Type*) [CommRing R] [Algebra ℂ R] (φ : R →ₐ[ℂ] ℂ) (t : R)
    (ht : φ t = 0) (hreg : Function.Injective (fun x : R => t * x))
    (N : ℕ) (p : Polynomial ℂ) :
    aeval t p ∈ Ideal.span {t ^ N} ↔ (Polynomial.X ^ N : Polynomial ℂ) ∣ p := by
  classical
  constructor
  · intro hp
    let M : Ideal R := Ideal.span {t ^ N}
    let r := p %ₘ (Polynomial.X ^ N)
    have hidentity : aeval t r + t ^ N * aeval t (p /ₘ (Polynomial.X ^ N)) = aeval t p := by
      have h := congrArg (aeval t) (modByMonic_add_div p (Polynomial.X ^ N))
      simpa only [map_add, map_mul, map_pow, aeval_X] using h
    have hr : aeval t r ∈ M := by
      have hm : t ^ N * aeval t (p /ₘ (Polynomial.X ^ N)) ∈ M :=
        M.mul_mem_right _ (Ideal.subset_span rfl)
      rw [← hidentity] at hp
      have h := M.sub_mem hp hm
      simpa only [add_sub_cancel_right] using h
    have hsum : (∑ i : Fin N, monomial i (r.coeff i)) = r :=
      sum_modByMonic_coeff (p := p) (monic_X_pow N) (by simp only [degree_X_pow, le_refl])
    have hval : (∑ i : Fin N, algebraMap ℂ R (r.coeff i) * t ^ (i : ℕ)) = aeval t r := by
      have he := congrArg (aeval t) hsum
      simpa only [map_sum, aeval_def, eval₂_monomial] using he
    have hz := s2e_parameter_jet_coefficients_zero R φ t ht hreg N
      (fun i => r.coeff i) (hval ▸ hr)
    have hr0 : r = 0 := by
      apply Polynomial.ext
      intro k
      change r.coeff k = 0
      by_cases hk : k < N
      · exact hz ⟨k, hk⟩
      · apply coeff_eq_zero_of_degree_lt
        have hd : r.degree < (N : WithBot ℕ) := by
          simpa only [degree_X_pow] using degree_modByMonic_lt p (monic_X_pow N)
        exact hd.trans_le (by exact_mod_cast Nat.le_of_not_gt hk)
    exact (modByMonic_eq_zero_iff_dvd (monic_X_pow N)).mp hr0
  · rintro ⟨q, rfl⟩
    simp only [map_mul, map_pow, aeval_X]
    exact (Ideal.span {t ^ N}).mul_mem_right _ (Ideal.subset_span rfl)

/-- Polynomial evaluation in the parameter represents every finite local jet.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
finite parameter expansions. -/
theorem s2e_parameter_jet_eval_surjective
    (R : Type*) [CommRing R] [Algebra ℂ R] [IsLocalRing R]
    (φ : R →ₐ[ℂ] ℂ) (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (N : ℕ) :
    Function.Surjective (aeval (Ideal.Quotient.mk (Ideal.span {t ^ N}) t) :
      Polynomial ℂ →ₐ[ℂ] R ⧸ Ideal.span {t ^ N}) := by
  classical
  let I : Ideal R := Ideal.span {t ^ N}
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨c, hc⟩ := s2e_local_parameter_jet_expansion R φ t ht N r
  let p : Polynomial ℂ := ∑ i : Fin N, monomial i (c i)
  refine ⟨p, ?_⟩
  change aeval ((Ideal.Quotient.mkₐ ℂ I) t) p = Ideal.Quotient.mk I r
  rw [aeval_algHom_apply]
  have heval : aeval t p = ∑ i : Fin N, algebraMap ℂ R (c i) * t ^ (i : ℕ) := by
    simp only [p, map_sum, aeval_def, eval₂_monomial]
  rw [heval]
  exact (Ideal.Quotient.eq.mpr hc).symm

/-- The polynomial coordinate map to a finite parameter neighbourhood has the
expected power ideal as its kernel.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
uniqueness of parameter expansions. -/
theorem s2e_parameter_jet_eval_kernel
    (R : Type*) [CommRing R] [Algebra ℂ R] (φ : R →ₐ[ℂ] ℂ) (t : R)
    (ht : φ t = 0) (hreg : Function.Injective (fun x : R => t * x)) (N : ℕ) :
    RingHom.ker (aeval (Ideal.Quotient.mk (Ideal.span {t ^ N}) t) :
      Polynomial ℂ →ₐ[ℂ] R ⧸ Ideal.span {t ^ N}).toRingHom =
      Ideal.span {(Polynomial.X ^ N : Polynomial ℂ)} := by
  let I : Ideal R := Ideal.span {t ^ N}
  ext p
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  change aeval ((Ideal.Quotient.mkₐ ℂ I) t) p = 0 ↔ (Polynomial.X ^ N : Polynomial ℂ) ∣ p
  rw [aeval_algHom_apply]
  change Ideal.Quotient.mk I (aeval t p) = 0 ↔ (Polynomial.X ^ N : Polynomial ℂ) ∣ p
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact s2e_parameter_polynomial_vanishing_iff R φ t ht hreg N p

/-- The finite neighbourhood of a regular local parameter has its polynomial
coordinate algebra, with nilpotents retained to the specified order.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
finite parameter expansions and their uniqueness. -/
noncomputable def s2e_parameter_jet_algEquiv
    (R : Type*) [CommRing R] [Algebra ℂ R] [IsLocalRing R]
    (φ : R →ₐ[ℂ] ℂ) (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (hreg : Function.Injective (fun x : R => t * x)) (N : ℕ) :
    (Polynomial ℂ ⧸ Ideal.span {(Polynomial.X ^ N : Polynomial ℂ)}) ≃ₐ[ℂ]
      (R ⧸ Ideal.span {t ^ N}) := by
  have hsurjφ : Function.Surjective φ := by
    intro z
    exact ⟨algebraMap ℂ R z, by simpa only [Algebra.algebraMap_self, RingHom.id_apply] using φ.commutes z⟩
  have hkerφ := IsLocalRing.ker_eq_maximalIdeal φ.toRingHom hsurjφ
  have ht0 : φ t = 0 := by
    change t ∈ RingHom.ker φ.toRingHom
    rw [hkerφ, ht]
    exact Ideal.subset_span rfl
  have hker := s2e_parameter_jet_eval_kernel R φ t ht0 hreg N
  have hsurj := s2e_parameter_jet_eval_surjective R φ t ht N
  exact (Ideal.quotientEquivAlgOfEq ℂ hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hsurj)

/-- The parameter coordinate equivalence is the specified polynomial evaluation map.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
finite parameter expansions. -/
theorem s2e_parameter_jet_algEquiv_mk
    (R : Type*) [CommRing R] [Algebra ℂ R] [IsLocalRing R]
    (φ : R →ₐ[ℂ] ℂ) (t : R) (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (hreg : Function.Injective (fun x : R => t * x)) (N : ℕ) (p : Polynomial ℂ) :
    s2e_parameter_jet_algEquiv R φ t ht hreg N
      (Ideal.Quotient.mk (Ideal.span {(Polynomial.X ^ N : Polynomial ℂ)}) p) =
      Ideal.Quotient.mk (Ideal.span {t ^ N}) (aeval t p) := by
  simp only [s2e_parameter_jet_algEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]
  exact aeval_algHom_apply (Ideal.Quotient.mkₐ ℂ (Ideal.span {t ^ N})) t p

end HodgeLean.Foundations.Program
