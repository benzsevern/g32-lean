import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairProjectiveKernel
import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairRealCoordinates
import Mathlib.Algebra.MvPolynomial.Eval

/-! Rational real coordinates of normalized Hermitian kernels.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.WitnessSelection.StageTwo

/-- Every real matrix coordinate is a polynomial numerator divided by the common mass polynomial.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_kernel_rational_coordinates {ι : Type*} [Fintype ι] {n : ℕ}
    (r s : ι → MvPolynomial (Fin n) ℝ) :
    let v : (Fin n → ℝ) → ι → ℂ := fun x i =>
      (MvPolynomial.eval x (r i) : ℂ) + (MvPolynomial.eval x (s i) : ℂ) * Complex.I
    ∃ (M : MvPolynomial (Fin n) ℝ)
      (P : Fin (Fintype.card ((ι × ι) ⊕ (ι × ι))) → MvPolynomial (Fin n) ℝ),
      (∀ x, MvPolynomial.eval x M = s2e_pair_vectorMass (v x)) ∧
      ∀ x k, s2e_pair_complexRealCoordinates
        (fun a : ι × ι => s2e_pair_projectiveKernel (v x) a.1 a.2) k =
          MvPolynomial.eval x (P k) / MvPolynomial.eval x M := by
  classical
  let v : (Fin n → ℝ) → ι → ℂ := fun x i =>
    (MvPolynomial.eval x (r i) : ℂ) + (MvPolynomial.eval x (s i) : ℂ) * Complex.I
  let M : MvPolynomial (Fin n) ℝ := ∑ i, (r i * r i + s i * s i)
  let P : Fin (Fintype.card ((ι × ι) ⊕ (ι × ι))) → MvPolynomial (Fin n) ℝ :=
    fun k => Sum.elim
      (fun a : ι × ι => r a.1 * r a.2 + s a.1 * s a.2)
      (fun a : ι × ι => s a.1 * r a.2 - r a.1 * s a.2)
      ((Fintype.equivFin ((ι × ι) ⊕ (ι × ι))).symm k)
  have hvre (x : Fin n → ℝ) (i : ι) : (v x i).re = MvPolynomial.eval x (r i) := by
    simp only [v, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  have hvim (x : Fin n → ℝ) (i : ι) : (v x i).im = MvPolynomial.eval x (s i) := by
    simp only [v, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  have hM (x : Fin n → ℝ) : MvPolynomial.eval x M = s2e_pair_vectorMass (v x) := by
    simp only [M, map_sum, MvPolynomial.eval_add, MvPolynomial.eval_mul,
      s2e_pair_vectorMass, Complex.normSq_apply, hvre, hvim]
  refine ⟨M, P, hM, ?_⟩
  intro x k
  change Sum.elim
    (fun a : ι × ι => (s2e_pair_projectiveKernel (v x) a.1 a.2).re)
    (fun a : ι × ι => (s2e_pair_projectiveKernel (v x) a.1 a.2).im)
    ((Fintype.equivFin ((ι × ι) ⊕ (ι × ι))).symm k) = _
  rw [hM]
  cases he : (Fintype.equivFin ((ι × ι) ⊕ (ι × ι))).symm k with
  | inl a =>
    simp only [Sum.elim_inl, s2e_pair_projectiveKernel, Complex.div_ofReal_re,
      Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, hvre, hvim,
      P, he, MvPolynomial.eval_add, MvPolynomial.eval_mul, mul_neg, sub_neg_eq_add]
  | inr a =>
    simp only [Sum.elim_inr, s2e_pair_projectiveKernel, Complex.div_ofReal_im,
      Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, hvre, hvim,
      P, he, map_sub, MvPolynomial.eval_mul, mul_neg, neg_add_eq_sub]

end HodgeLean.WitnessSelection.StageTwo
