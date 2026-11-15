import HodgeLean.Foundations.Program.MilneTensorDescent

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_principal_open_rational_extension {σ : Type*}
    (d p a b : MvPolynomial σ ℂ) (hd : d ≠ 0) (hp : p ≠ 0) (k l : ℕ)
    (F G : (σ → ℂ) → ℂ)
    (hF : ∀ x, MvPolynomial.eval x d ≠ 0 →
      MvPolynomial.eval x a = MvPolynomial.eval x d ^ k * F x)
    (hG : ∀ x, MvPolynomial.eval x d ≠ 0 →
      MvPolynomial.eval x b = MvPolynomial.eval x d ^ l * G x)
    (h : ∀ x, MvPolynomial.eval x d ≠ 0 → MvPolynomial.eval x p ≠ 0 → F x = G x) :
    ∀ x, MvPolynomial.eval x d ≠ 0 → F x = G x := by
  have hpoly : a * d ^ l = b * d ^ k := by
    apply sub_eq_zero.mp
    apply m1b_polynomial_zero_on_principal_open _ (d * p) (mul_ne_zero hd hp)
    intro x hx
    have hx' : MvPolynomial.eval x d ≠ 0 ∧ MvPolynomial.eval x p ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff] using hx
    rw [map_sub, map_mul, map_mul, map_pow, map_pow,
      hF x hx'.1, hG x hx'.1, h x hx'.1 hx'.2]
    ring
  intro x hx
  have he := congrArg (MvPolynomial.eval x) hpoly
  rw [map_mul, map_mul, map_pow, map_pow, hF x hx, hG x hx] at he
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero k hx) (pow_ne_zero l hx))
  calc
    (MvPolynomial.eval x d ^ k * MvPolynomial.eval x d ^ l) * F x =
        (MvPolynomial.eval x d ^ k * F x) * MvPolynomial.eval x d ^ l := by ring
    _ = (MvPolynomial.eval x d ^ l * G x) * MvPolynomial.eval x d ^ k := he
    _ = (MvPolynomial.eval x d ^ k * MvPolynomial.eval x d ^ l) * G x := by ring

end HodgeLean.Foundations.Program
