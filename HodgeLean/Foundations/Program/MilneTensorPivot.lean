import HodgeLean.Foundations.Program.MilneTensorDescent
import HodgeLean.Foundations.Program.MilneTensorFormPolynomial
import Mathlib.Algebra.MvPolynomial.Division

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_variable_relprime {σ : Type*} (i j : σ) (hij : i ≠ j) :
    IsRelPrime (MvPolynomial.X i : MvPolynomial σ ℂ) (MvPolynomial.X j) := by
  apply (MvPolynomial.X_prime (i := i)).irreducible.isRelPrime_iff_not_dvd.mpr
  simpa only [MvPolynomial.X_dvd_X] using hij

theorem m1b_variable_power_gluing {σ : Type*} (i j : σ) (hij : i ≠ j)
    (a b d : MvPolynomial σ ℂ) (hd : d ≠ 0) (k l : ℕ)
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x d ≠ 0 → x i ≠ 0 → x j ≠ 0 →
      MvPolynomial.eval x a * x j ^ l = MvPolynomial.eval x b * x i ^ k) :
    ∃ c : MvPolynomial σ ℂ,
      a = MvPolynomial.X i ^ k * c ∧ b = MvPolynomial.X j ^ l * c := by
  apply m1b_relprime_common_quotient _ _ a b
    (pow_ne_zero k (MvPolynomial.X_ne_zero i)) (m1b_variable_relprime i j hij).pow
  apply m1b_polynomial_cross_on_dense_domain _ _ a b
    (d * (MvPolynomial.X i * MvPolynomial.X j))
    (pow_ne_zero k (MvPolynomial.X_ne_zero i))
    (pow_ne_zero l (MvPolynomial.X_ne_zero j))
    (mul_ne_zero hd (mul_ne_zero (MvPolynomial.X_ne_zero i) (MvPolynomial.X_ne_zero j)))
  intro x hx _ _
  have hx' : MvPolynomial.eval x d ≠ 0 ∧ x i ≠ 0 ∧ x j ≠ 0 := by
    simpa only [map_mul, MvPolynomial.eval_X, mul_ne_zero_iff] using hx
  simpa only [map_pow, MvPolynomial.eval_X] using h x hx'.1 hx'.2.1 hx'.2.2

theorem m1b_two_pivot_polynomial {σ : Type*} (i j : σ) (hij : i ≠ j)
    (a b d : MvPolynomial σ ℂ) (hd : d ≠ 0) (k l : ℕ)
    (F : (σ → ℂ) → ℂ)
    (ha : ∀ x, MvPolynomial.eval x d ≠ 0 → x i ≠ 0 →
      MvPolynomial.eval x a = x i ^ k * F x)
    (hb : ∀ x, MvPolynomial.eval x d ≠ 0 → x j ≠ 0 →
      MvPolynomial.eval x b = x j ^ l * F x) :
    ∃ c : MvPolynomial σ ℂ, ∀ x, MvPolynomial.eval x d ≠ 0 →
      (x i ≠ 0 ∨ x j ≠ 0) → MvPolynomial.eval x c = F x := by
  obtain ⟨c, hac, hbc⟩ := m1b_variable_power_gluing i j hij a b d hd k l (by
    intro x hx hi hj
    rw [ha x hx hi, hb x hx hj]
    ring)
  refine ⟨c, ?_⟩
  intro x hx h
  rcases h with hi | hj
  · have he := ha x hx hi
    rw [hac, map_mul, map_pow, MvPolynomial.eval_X] at he
    exact mul_left_cancel₀ (pow_ne_zero k hi) he
  · have he := hb x hx hj
    rw [hbc, map_mul, map_pow, MvPolynomial.eval_X] at he
    exact mul_left_cancel₀ (pow_ne_zero l hj) he

theorem m1b_symmetric_pivots_relprime (d : ℕ) (i j : Fin d) (hij : i ≠ j) :
    IsRelPrime (m1b_symmetricVariables d i i) (m1b_symmetricVariables d j j) := by
  apply m1b_variable_relprime
  intro h
  rcases Sym2.eq_iff.mp h with h | h
  · exact hij h.1
  · exact hij h.1

theorem m1b_alternating_pivots_relprime (d : ℕ)
    (p q : {a : Fin d × Fin d // a.1 < a.2}) (hpq : p ≠ q) :
    IsRelPrime (m1b_alternatingVariables d p.val.1 p.val.2)
      (m1b_alternatingVariables d q.val.1 q.val.2) := by
  simp only [m1b_alternatingVariables, dite_eq_left p.property, dite_eq_left q.property]
  exact m1b_variable_relprime p q hpq

end HodgeLean.Foundations.Program
