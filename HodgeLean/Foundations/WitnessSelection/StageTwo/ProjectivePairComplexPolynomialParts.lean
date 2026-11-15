import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Complex.Basic

/-! Real polynomial descriptions of complex polynomial evaluations.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.WitnessSelection.StageTwo

/-- Substitution of polynomial real and imaginary coordinates has polynomial real and imaginary parts.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_complex_polynomial_parts {ι σ : Type*}
    (p : MvPolynomial ι ℂ) (r s : ι → MvPolynomial σ ℝ) :
    ∃ R S : MvPolynomial σ ℝ, ∀ x : σ → ℝ,
      (MvPolynomial.eval (fun i =>
        (MvPolynomial.eval x (r i) : ℂ) + (MvPolynomial.eval x (s i) : ℂ) * Complex.I) p).re =
          MvPolynomial.eval x R ∧
      (MvPolynomial.eval (fun i =>
        (MvPolynomial.eval x (r i) : ℂ) + (MvPolynomial.eval x (s i) : ℂ) * Complex.I) p).im =
          MvPolynomial.eval x S := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨MvPolynomial.C c.re, MvPolynomial.C c.im, ?_⟩
    intro x
    simp only [MvPolynomial.eval_C, and_self]
  | add p q hp hq =>
    obtain ⟨R, S, hRS⟩ := hp
    obtain ⟨T, U, hTU⟩ := hq
    refine ⟨R + T, S + U, ?_⟩
    intro x
    simp only [MvPolynomial.eval_add, Complex.add_re, Complex.add_im,
      (hRS x).1, (hRS x).2, (hTU x).1, (hTU x).2, and_self]
  | mul_X p i hp =>
    obtain ⟨R, S, hRS⟩ := hp
    refine ⟨R * r i - S * s i, R * s i + S * r i, ?_⟩
    intro x
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      zero_sub, sub_zero, zero_add, add_zero, (hRS x).1, (hRS x).2,
      map_sub, MvPolynomial.eval_add, and_self]

end HodgeLean.WitnessSelection.StageTwo
