import HodgeLean.Foundations.Program.G32Native.PELCayleyPolynomialChart

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
namespace HodgeLean.Foundations
variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Polynomial coordinates for the complex span of a real matrix subspace. -/
def pel_real_subspace_polynomial
    {L : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} (b : Module.Basis ι ℝ L) :
    Matrix (Fin n) (Fin n) (MvPolynomial ι ℂ) :=
  fun i j => ∑ a, C (((b a).val i j : ℝ) : ℂ) * X a

/-- Real parameters in this polynomial chart are exactly real basis combinations. -/
theorem pel_real_subspace_polynomial_eval_real
    {L : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} (b : Module.Basis ι ℝ L)
    (t : ι → ℝ) :
    (eval (fun i => (t i : ℂ))).mapMatrix (pel_real_subspace_polynomial b) =
      ((b.equivFun.symm t).val).map Complex.ofReal := by
  ext i j
  have he : (b.equivFun.symm t).val i j = ∑ a, t a * (b a).val i j := by
    let l : L →ₗ[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).comp L.subtype
    have h := congrArg l (b.equivFun_symm_apply t)
    simpa only [map_sum, map_smul, smul_eq_mul, l, LinearMap.comp_apply,
      Matrix.entryLinearMap_apply, Submodule.subtype_apply] using h
  simp only [pel_real_subspace_polynomial, RingHom.mapMatrix_apply, map_sum,
    map_mul, eval_C, eval_X, Matrix.map_apply, he, Complex.ofReal_sum,
    Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- A complex matrix whose real and imaginary parts belong to the real
subspace has coordinates in its complex polynomial parametrization. -/
theorem pel_real_subspace_polynomial_surjective
    {L : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} (b : Module.Basis ι ℝ L)
    (Y : Matrix (Fin n) (Fin n) ℂ)
    (hR : Y.map Complex.re ∈ L) (hI : Y.map Complex.im ∈ L) :
    ∃ z : ι → ℂ, (eval z).mapMatrix (pel_real_subspace_polynomial b) = Y := by
  let A : L := ⟨Y.map Complex.re, hR⟩
  let B : L := ⟨Y.map Complex.im, hI⟩
  refine ⟨fun a => (b.repr A a : ℂ) + Complex.I * (b.repr B a : ℂ), ?_⟩
  ext i j
  let l : L →ₗ[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).comp L.subtype
  have hr := congrArg l (b.sum_repr A)
  have hi := congrArg l (b.sum_repr B)
  simp only [map_sum, map_smul, smul_eq_mul] at hr hi
  change (∑ a, b.repr A a * (b a).val i j) = A.val i j at hr
  change (∑ a, b.repr B a * (b a).val i j) = B.val i j at hi
  have hrc := congrArg Complex.ofReal hr
  have hic := congrArg Complex.ofReal hi
  simp only [Complex.ofReal_sum, Complex.ofReal_mul] at hrc hic
  change eval _ (∑ a, C ((b a).val i j : ℂ) * X a) = Y i j
  simp only [map_sum, map_mul, eval_C, eval_X]
  calc
    _ = (∑ a, (b.repr A a : ℂ) * ((b a).val i j : ℂ)) +
        Complex.I * (∑ a, (b.repr B a : ℂ) * ((b a).val i j : ℂ)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro a ha <;> ring
    _ = (Y i j).re + Complex.I * (Y i j).im := by rw [hrc, hic]; rfl
    _ = Y i j := by simpa only [mul_comm Complex.I] using Complex.re_add_im (Y i j)

end HodgeLean.Foundations
