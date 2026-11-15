import HodgeLean.Foundations.Program.TorusAlgebraizationB52Multiplicative
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Avoidance

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b52_exponential_of_balanced_quotient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f p : E → ℂ) (hf : Differentiable ℂ f) (hp : Differentiable ℂ p)
    (hne : ∀ x, f x ≠ 0 → p x ≠ 0) (k : E) (C : ℂ)
    (hprod : ∀ x, f x ≠ 0 → ∀ y, f y ≠ 0 → f (k - x - y) ≠ 0 →
      (p x / f x) * (p y / f y) * (p (k - x - y) / f (k - x - y)) = C)
    (b t : E) (hb : f b ≠ 0) (ht : f t ≠ 0) (hbt : f (k - t - b) ≠ 0) :
    ∃ (L : E →L[ℂ] ℂ) (d : ℂ), d ≠ 0 ∧ ∀ x, p x = d * Complex.exp (L x) * f x := by
  let U : Set E := {x | f x ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage hf.continuous
  have hg : DifferentiableOn ℂ (fun x ↦ p x / f x) U := by
    intro x hx
    have hi := (hasDerivAt_inv hx).hasFDerivAt.comp x (hf x).hasFDerivAt
    simpa only [Function.comp_def, div_eq_mul_inv, Pi.mul_def] using
      ((hp x).hasFDerivAt.mul hi).differentiableAt.differentiableWithinAt (s := U)
  obtain ⟨L, d, W, hd, hW, hWn, hWU, hval⟩ :=
    b52_three_product_locally_exponential (fun x ↦ p x / f x) hU hg
      (fun x hx ↦ div_ne_zero (hne x hx) hx) k C hprod b t hb ht hbt
  let q : E → ℂ := fun x ↦ p x - d * Complex.exp (L x) * f x
  have hq : Differentiable ℂ q := hp.sub ((L.differentiable.cexp.const_mul d).mul hf)
  have hq0 : q = 0 := by
    by_contra hn
    obtain ⟨x, hx, hxW⟩ := (b52_dense_nonzero hq hn).exists_mem_open hW hWn
    apply hx
    exact sub_eq_zero.mpr ((div_eq_iff (hWU hxW)).mp (hval x hxW))
  refine ⟨L, d, hd, fun x ↦ sub_eq_zero.mp ?_⟩
  exact congrFun hq0 x

end HodgeLean.Foundations.Program
