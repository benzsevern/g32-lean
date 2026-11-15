import HodgeLean.Foundations.Program.NumeratorJetAnalytic
import HodgeLean.Foundations.Program.NumeratorJetFixedInverse

/-! # Division by the fixed factors through truncated expansions at infinity

For a monic `B` and a polynomial `Λ` with `X¹³ − B Λ` of degree below `deg B` (the expansion of
`1/B` at `∞` through `s⁻¹³`), the quotient `D /ₘ B` of any `D` of degree at most `13` is read off
from `D Λ`. Synthetic division by a moving factor `X − t` gives the coefficients of the erased
branch polynomial from those of the branch polynomial. Together with `b65e_product_expand` this
writes every coefficient of the polynomial part of a frame product as a finite expression in the
coefficients of the branch polynomial, the frames, the left vectors and the moving poles.
-/

noncomputable section
open Polynomial
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- Quotients by a monic polynomial from a truncated expansion of its inverse at infinity. -/
theorem b65e_divByMonic_laurent (D B Λ : ℂ[X]) (hB : B.Monic) (hD : D.natDegree ≤ 13)
    (hΛ : ∀ m, B.natDegree ≤ m → (X ^ 13 - B * Λ).coeff m = 0) (j : ℕ) :
    (D /ₘ B).coeff j = (D * Λ).coeff (13 + j) := by
  have hX : (X ^ 13 : ℂ[X]).Monic := monic_X_pow 13
  obtain ⟨P, hP⟩ : ∃ P, P = (D * Λ) /ₘ X ^ 13 := ⟨_, rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1, R1 = (D * Λ) %ₘ X ^ 13 := ⟨_, rfl⟩
  have h1 : R1 + X ^ 13 * P = D * Λ := by rw [hP, hR1]; exact modByMonic_add_div _ _
  have hR1deg : ∀ l, 13 ≤ l → R1.coeff l = 0 := by
    have h := degree_modByMonic_lt (D * Λ) hX
    rw [degree_X_pow, ← hR1] at h
    exact (degree_lt_iff_coeff_zero _ _).1 h
  have hkey : X ^ 13 * (D - B * P) = D * (X ^ 13 - B * Λ) + B * R1 := by
    have h2 : X ^ 13 * P = D * Λ - R1 := by rw [← h1]; ring
    calc X ^ 13 * (D - B * P) = X ^ 13 * D - B * (X ^ 13 * P) := by ring
      _ = _ := by rw [h2]; ring
  have hdeg : (D - B * P).degree < B.degree := by
    rw [degree_eq_natDegree hB.ne_zero, degree_lt_iff_coeff_zero]
    intro m hm
    have hc := congrArg (fun f : ℂ[X] ↦ f.coeff (m + 13)) hkey
    simp only [coeff_X_pow_mul] at hc
    rw [hc, coeff_add, coeff_mul, coeff_mul]
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro x hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      by_cases h : x.2 ≤ 12
      · rw [coeff_eq_zero_of_natDegree_lt (p := B) (by omega), zero_mul]
      · rw [hR1deg x.2 (by omega), mul_zero]
    · intro x hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      by_cases h : x.1 ≤ 13
      · rw [hΛ x.2 (by omega), mul_zero]
      · rw [coeff_eq_zero_of_natDegree_lt (p := D) (by omega), zero_mul]
  have hq := (div_modByMonic_unique P (D - B * P) hB ⟨by ring, hdeg⟩).1
  rw [hq]
  have hc := congrArg (fun f : ℂ[X] ↦ f.coeff (j + 13)) h1
  simp only [coeff_add, coeff_X_pow_mul, hR1deg (j + 13) (by omega), zero_add] at hc
  rw [hc, add_comm]

/-- Quotient by a product of monic polynomials, one factor at a time. -/
theorem b65e_divByMonic_mul (f q r : ℂ[X]) (hq : q.Monic) (hr : r.Monic) :
    f /ₘ (q * r) = (f /ₘ q) /ₘ r := by
  have h1 := modByMonic_add_div f q
  have h2 := modByMonic_add_div (f /ₘ q) r
  apply (div_modByMonic_unique ((f /ₘ q) /ₘ r) (f %ₘ q + q * ((f /ₘ q) %ₘ r))
    (hq.mul hr) ⟨?_, ?_⟩).1
  · calc f %ₘ q + q * ((f /ₘ q) %ₘ r) + q * r * ((f /ₘ q) /ₘ r)
        = f %ₘ q + q * ((f /ₘ q) %ₘ r + r * ((f /ₘ q) /ₘ r)) := by ring
      _ = f := by rw [h2, h1]
  · rw [degree_eq_natDegree (hq.mul hr).ne_zero]
    rw [hq.natDegree_mul hr, degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_add, coeff_mul]
    have hq' := (degree_lt_iff_coeff_zero _ _).1
      (by rw [← degree_eq_natDegree hq.ne_zero]; exact degree_modByMonic_lt f hq)
    have hr' := (degree_lt_iff_coeff_zero _ _).1
      (by rw [← degree_eq_natDegree hr.ne_zero]; exact degree_modByMonic_lt (f /ₘ q) hr)
    rw [hq' m (by omega), zero_add]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h : x.1 ≤ q.natDegree
    · rw [hr' x.2 (by omega), mul_zero]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

/-- Synthetic division by a linear factor: coefficients of the cofactor. -/
theorem b65e_synthetic (t : ℂ) (E D : ℂ[X]) (h : (X - C t) * E = D) (hE : E.natDegree ≤ 12) :
    ∀ k, k ≤ 13 → E.coeff k = ∑ m ∈ Finset.range (13 - k), D.coeff (k + 1 + m) * t ^ m := by
  have hs : ∀ s, s ≤ 13 → E.coeff (13 - s) =
      ∑ m ∈ Finset.range s, D.coeff (14 - s + m) * t ^ m := by
    intro s
    induction s with
    | zero =>
      intro _
      simpa using coeff_eq_zero_of_natDegree_lt (by omega : E.natDegree < 13)
    | succ s ih =>
      intro hs
      have hc : D.coeff (12 - s + 1) = E.coeff (12 - s) - t * E.coeff (12 - s + 1) := by
        rw [← h, coeff_X_sub_C_mul]
      have e1 : 12 - s + 1 = 13 - s := by omega
      rw [e1] at hc
      rw [show 13 - (s + 1) = 12 - s by omega, Finset.sum_range_succ', pow_zero, mul_one,
        show 14 - (s + 1) + 0 = 13 - s by omega]
      have : E.coeff (12 - s) = D.coeff (13 - s) + t * E.coeff (13 - s) := by
        rw [hc]; ring
      rw [this, ih (by omega), Finset.mul_sum, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      rw [show 14 - (s + 1) + (m + 1) = 14 - s + m by omega, pow_succ]
      ring
  intro k hk
  have := hs (13 - k) (by omega)
  rw [show 13 - (13 - k) = k by omega] at this
  rw [this]
  apply Finset.sum_congr rfl
  intro m _
  rw [show 14 - (13 - k) + m = k + 1 + m by omega]

/-- Coefficient of `s⁻ᵘ` in the expansion of `(s − α)^{−k}` at infinity. -/
def b65e_LQ (a : Fin 9) (u : ℕ) : ℚ :=
  if b65k_poleOrder a ≤ u then
    ((u - 1).choose (b65k_poleOrder a - 1) : ℚ) *
      b65e_fixedPoleQ (b65k_poleIndex a) ^ (u - b65k_poleOrder a)
  else 0

/-- The weight of the coefficient `k` of a polynomial in the coefficient `j` of its quotient by
the fixed factor `a`. -/
def b65e_LamQ (a : Fin 9) (k j : ℕ) : ℚ := if j ≤ k then b65e_LQ a (k - j) else 0

/-- The truncated expansion `Σ_{u ≤ 13} L_u X^{13−u}` of `X¹³ / F_a`. -/
def b65e_Lambda (a : Fin 9) : ℂ[X] :=
  ∑ u ∈ Finset.range 14, C ((b65e_LQ a u : ℚ) : ℂ) * X ^ (13 - u)

theorem b65e_Lambda_coeff (a : Fin 9) (l : ℕ) :
    (b65e_Lambda a).coeff l = if l ≤ 13 then ((b65e_LQ a (13 - l) : ℚ) : ℂ) else 0 := by
  simp only [b65e_Lambda, finsetSum_coeff, coeff_C_mul_X_pow]
  split_ifs with hl
  · rw [Finset.sum_eq_single (13 - l)]
    · have h1 : l = 13 - (13 - l) := by omega
      simp only [← h1, ↓reduceIte]
    · intro u hu hne
      have := Finset.mem_range.mp hu
      have h1 : ¬ l = 13 - u := by omega
      simp only [h1, ↓reduceIte]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · apply Finset.sum_eq_zero
    intro u hu
    have h1 : ¬ l = 13 - u := by omega
    simp only [h1, ↓reduceIte]

/-- Rational form of the coefficient `m` of `X¹³ − F_a Λ_a`. -/
def b65e_LamCertQ (a : Fin 9) (m : ℕ) : ℚ :=
  (if m = 13 then 1 else 0) - ∑ i ∈ Finset.range (m + 1),
    (-b65e_fixedPoleQ (b65k_poleIndex a)) ^ (b65k_poleOrder a - i) *
      ((b65k_poleOrder a).choose i : ℚ) *
      (if m - i ≤ 13 then b65e_LQ a (13 - (m - i)) else 0)

theorem b65e_LamCert_coeff (a : Fin 9) (m : ℕ) :
    (X ^ 13 - b65e_fixedFactor a * b65e_Lambda a).coeff m = ((b65e_LamCertQ a m : ℚ) : ℂ) := by
  rw [coeff_sub, coeff_X_pow, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [b65e_fixedFactor, sub_eq_add_neg (X : ℂ[X]), ← map_neg C, coeff_X_add_C_pow,
    b65e_Lambda_coeff, b65e_LamCertQ]
  push_cast
  rw [← b65e_fixedPoleQ_cast]
  congr 1
  · split_ifs <;> simp_all
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp

set_option maxHeartbeats 400000 in
theorem b65e_LamCertQ_zero : ∀ a : Fin 9, ∀ m : Fin 17,
    b65k_poleOrder a ≤ m.val → b65e_LamCertQ a m.val = 0 := by
  decide +kernel

theorem b65e_Lambda_cert (a : Fin 9) (m : ℕ) (hm : (b65e_fixedFactor a).natDegree ≤ m) :
    (X ^ 13 - b65e_fixedFactor a * b65e_Lambda a).coeff m = 0 := by
  have hdeg : (b65e_fixedFactor a).natDegree = b65k_poleOrder a := by
    rw [b65e_fixedFactor, natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [hdeg] at hm
  rw [b65e_LamCert_coeff]
  by_cases h : m < 17
  · rw [b65e_LamCertQ_zero a ⟨m, h⟩ hm, Rat.cast_zero]
  · have hk : b65k_poleOrder a ≤ 3 := by fin_cases a <;> decide
    have h13 : ¬ m = 13 := by omega
    rw [b65e_LamCertQ, Finset.sum_eq_zero, sub_zero]
    · simp only [h13, ↓reduceIte, Rat.cast_zero]
    intro i _
    by_cases hi : i ≤ b65k_poleOrder a
    · have h1 : ¬ m - i ≤ 13 := by omega
      simp only [h1, ↓reduceIte, mul_zero]
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp

/-- Coefficients of the quotient by a fixed factor of a polynomial of degree below `N ≤ 14`. -/
theorem b65e_divFixed_coeff (a : Fin 9) (f : ℂ[X]) (N : ℕ) (hN : N ≤ 14)
    (hf : f.natDegree < N) (j : ℕ) :
    (f /ₘ b65e_fixedFactor a).coeff j =
      ∑ k ∈ Finset.range N, f.coeff k * ((b65e_LamQ a k j : ℚ) : ℂ) := by
  rw [b65e_divByMonic_laurent f _ _ (b65e_fixedFactor_monic a) (by omega)
    (b65e_Lambda_cert a), coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  symm
  calc _ = ∑ k ∈ Finset.range (13 + j).succ, f.coeff k * ((b65e_LamQ a k j : ℚ) : ℂ) := by
        apply Finset.sum_subset
        · intro k hk
          simp only [Finset.mem_range] at hk ⊢
          omega
        · intro k _ hk'
          simp only [Finset.mem_range] at hk'
          rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k ≤ 13
        · rw [b65e_Lambda_coeff, b65e_LamQ]
          by_cases hjk : j ≤ k
          · have h1 : 13 + j - k ≤ 13 := by omega
            simp only [h1, hjk, ↓reduceIte, show 13 - (13 + j - k) = k - j by omega]
          · have h1 : ¬ 13 + j - k ≤ 13 := by omega
            simp only [h1, hjk, ↓reduceIte, Rat.cast_zero]
        · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, zero_mul]

end HodgeLean.Foundations.Program
