import Mathlib.Algebra.MvPolynomial.Funext
import HodgeLean.Foundations.Program.MilneTensorPolynomial
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Coprime.Lemmas

noncomputable section
namespace HodgeLean.Foundations.Program
variable {R : Type*} [CommRing R] [IsDomain R] [DecompositionMonoid R]

omit [IsDomain R] in
theorem m1b_relprime_cross_divides (p q a b : R) (hpq : IsRelPrime p q)
    (h : a * q = b * p) : p ∣ a := by
  apply hpq.dvd_of_dvd_mul_right
  rw [h]
  exact dvd_mul_left p b

omit [IsDomain R] in
theorem m1b_two_denominator_descent {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (p q a b : R) (hp : p ≠ 0) (hpq : IsRelPrime p q) (z : K)
    (ha : algebraMap R K p * z = algebraMap R K a)
    (hb : algebraMap R K q * z = algebraMap R K b) :
    ∃ c : R, z = algebraMap R K c := by
  have hcross : a * q = b * p := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_mul, ← ha, ← hb]
    ring
  obtain ⟨c, hc⟩ := m1b_relprime_cross_divides p q a b hpq hcross
  refine ⟨c, ?_⟩
  have hp' : algebraMap R K p ≠ 0 := by
    intro h
    apply hp
    apply IsFractionRing.injective R K
    simpa only [map_zero] using h
  apply mul_left_cancel₀ hp'
  rw [ha, hc, map_mul]

theorem m1b_two_chart_descent {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (p q a b : R) (hp : p ≠ 0) (hpq : IsRelPrime p q) (i j : ℕ) (z : K)
    (ha : (algebraMap R K p) ^ i * z = algebraMap R K a)
    (hb : (algebraMap R K q) ^ j * z = algebraMap R K b) :
    ∃ c : R, z = algebraMap R K c := by
  apply m1b_two_denominator_descent (p ^ i) (q ^ j) a b (pow_ne_zero i hp) hpq.pow z
  · simpa only [map_pow] using ha
  · simpa only [map_pow] using hb

theorem m1b_relprime_common_quotient (p q a b : R) (hp : p ≠ 0)
    (hpq : IsRelPrime p q) (h : a * q = b * p) :
    ∃ c : R, a = p * c ∧ b = q * c := by
  obtain ⟨c, hc⟩ := m1b_relprime_cross_divides p q a b hpq h
  have hh : p * (c * q) = p * b := by
    calc
      p * (c * q) = a * q := by rw [hc, mul_assoc]
      _ = b * p := h
      _ = p * b := mul_comm _ _
  have hcb : c * q = b := mul_left_cancel₀ hp hh
  exact ⟨c, hc, hcb.symm.trans (mul_comm _ _)⟩

theorem m1b_polynomial_zero_on_principal_open {σ : Type*} (p q : MvPolynomial σ ℂ)
    (hq : q ≠ 0) (h : ∀ x : σ → ℂ, MvPolynomial.eval x q ≠ 0 → MvPolynomial.eval x p = 0) :
    p = 0 := by
  have hpq : p * q = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x q = 0
    · rw [hx, mul_zero]
    · rw [h x hx, zero_mul]
  exact (mul_eq_zero.mp hpq).resolve_right hq

theorem m1b_polynomial_cross_of_overlap {σ : Type*} (p q a b : MvPolynomial σ ℂ)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x p ≠ 0 → MvPolynomial.eval x q ≠ 0 →
      MvPolynomial.eval x a * MvPolynomial.eval x q =
        MvPolynomial.eval x b * MvPolynomial.eval x p) : a * q = b * p := by
  apply sub_eq_zero.mp
  apply m1b_polynomial_zero_on_principal_open _ (p * q) (mul_ne_zero hp hq)
  intro x hx
  have hx' : MvPolynomial.eval x p ≠ 0 ∧ MvPolynomial.eval x q ≠ 0 :=
    mul_ne_zero_iff.mp (by simpa only [map_mul] using hx)
  rw [map_sub, map_mul, map_mul, h x hx'.1 hx'.2, sub_self]

theorem m1b_polynomial_chart_gluing {σ : Type*} (p q a b : MvPolynomial σ ℂ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hpq : IsRelPrime p q)
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x p ≠ 0 → MvPolynomial.eval x q ≠ 0 →
      MvPolynomial.eval x a * MvPolynomial.eval x q =
        MvPolynomial.eval x b * MvPolynomial.eval x p) :
    ∃ c : MvPolynomial σ ℂ, a = p * c ∧ b = q * c := by
  exact m1b_relprime_common_quotient p q a b hp hpq
    (m1b_polynomial_cross_of_overlap p q a b hp hq h)

theorem m1b_polynomial_cross_on_dense_domain {σ : Type*}
    (p q a b d : MvPolynomial σ ℂ) (hp : p ≠ 0) (hq : q ≠ 0) (hd : d ≠ 0)
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x d ≠ 0 →
      MvPolynomial.eval x p ≠ 0 → MvPolynomial.eval x q ≠ 0 →
      MvPolynomial.eval x a * MvPolynomial.eval x q =
        MvPolynomial.eval x b * MvPolynomial.eval x p) : a * q = b * p := by
  apply sub_eq_zero.mp
  apply m1b_polynomial_zero_on_principal_open _ (d * (p * q))
    (mul_ne_zero hd (mul_ne_zero hp hq))
  intro x hx
  have hx' : MvPolynomial.eval x d ≠ 0 ∧
      MvPolynomial.eval x p ≠ 0 ∧ MvPolynomial.eval x q ≠ 0 := by
    simpa only [map_mul, mul_ne_zero_iff] using hx
  rw [map_sub, map_mul, map_mul, h x hx'.1 hx'.2.1 hx'.2.2, sub_self]

theorem m1b_polynomial_family_gluing {σ ι : Type*}
    (D N : ι → MvPolynomial σ ℂ) (d : MvPolynomial σ ℂ) (i₀ i₁ : ι)
    (hD : ∀ i, D i ≠ 0) (hd : d ≠ 0) (hc : IsRelPrime (D i₀) (D i₁))
    (h : ∀ i j (x : σ → ℂ), MvPolynomial.eval x d ≠ 0 →
      MvPolynomial.eval x (D i) ≠ 0 → MvPolynomial.eval x (D j) ≠ 0 →
      MvPolynomial.eval x (N i) * MvPolynomial.eval x (D j) =
        MvPolynomial.eval x (N j) * MvPolynomial.eval x (D i)) :
    ∃ c : MvPolynomial σ ℂ, ∀ i, N i = D i * c := by
  have hcross (i j : ι) : N i * D j = N j * D i :=
    m1b_polynomial_cross_on_dense_domain (D i) (D j) (N i) (N j) d
      (hD i) (hD j) hd (h i j)
  obtain ⟨c, h₀, _⟩ := m1b_relprime_common_quotient (D i₀) (D i₁) (N i₀) (N i₁)
    (hD i₀) hc (hcross i₀ i₁)
  refine ⟨c, ?_⟩
  intro i
  apply mul_left_cancel₀ (hD i₀)
  calc
    D i₀ * N i = N i * D i₀ := mul_comm _ _
    _ = N i₀ * D i := hcross i i₀
    _ = D i₀ * (D i * c) := by rw [h₀]; ring

theorem m1b_polynomial_chart_cover_extension {σ ι : Type*}
    (D N : ι → MvPolynomial σ ℂ) (d : MvPolynomial σ ℂ) (F : (σ → ℂ) → ℂ)
    (i₀ i₁ : ι) (hD : ∀ i, D i ≠ 0) (hd : d ≠ 0)
    (hc : IsRelPrime (D i₀) (D i₁))
    (hlocal : ∀ i x, MvPolynomial.eval x d ≠ 0 → MvPolynomial.eval x (D i) ≠ 0 →
      MvPolynomial.eval x (N i) = MvPolynomial.eval x (D i) * F x)
    (hcover : ∀ x, MvPolynomial.eval x d ≠ 0 → ∃ i, MvPolynomial.eval x (D i) ≠ 0) :
    ∃ p : MvPolynomial σ ℂ, ∀ x, MvPolynomial.eval x d ≠ 0 →
      MvPolynomial.eval x p = F x := by
  obtain ⟨p, hp⟩ := m1b_polynomial_family_gluing D N d i₀ i₁ hD hd hc (by
    intro i j x hx hi hj
    rw [hlocal i x hx hi, hlocal j x hx hj]
    ring)
  refine ⟨p, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx
  apply mul_left_cancel₀ hi
  rw [← map_mul, ← hp i]
  exact hlocal i x hx hi

end HodgeLean.Foundations.Program
