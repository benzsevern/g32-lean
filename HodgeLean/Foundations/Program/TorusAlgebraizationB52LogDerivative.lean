import HodgeLean.Foundations.Program.TorusAlgebraizationB52Functional
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Avoidance
import HodgeLean.Foundations.AnalyticDivisorAlgebraic2

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b52_affine_of_balanced_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f p : E → ℂ) (hf : Differentiable ℂ f) (hp : Differentiable ℂ p)
    (k : E) (C : ℂ)
    (hsum : ∀ x, f x ≠ 0 → ∀ y, f y ≠ 0 → f (k - x - y) ≠ 0 →
      p x / f x + p y / f y + p (k - x - y) / f (k - x - y) = C)
    (b t : E) (hb : f b ≠ 0) (ht : f t ≠ 0) (hbt : f (k - t - b) ≠ 0) :
    ∃ (L : E →L[ℂ] ℂ) (d : ℂ), ∀ x, p x = (L x + d) * f x := by
  let U : Set E := {x | f x ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage hf.continuous
  have hg : DifferentiableOn ℂ (fun x ↦ p x / f x) U := by
    intro x hx
    have hi := (hasDerivAt_inv hx).hasFDerivAt.comp x (hf x).hasFDerivAt
    simpa only [Function.comp_def, div_eq_mul_inv, Pi.mul_def] using
      ((hp x).hasFDerivAt.mul hi).differentiableAt.differentiableWithinAt (s := U)
  obtain ⟨L, d, W, hW, hWn, hWU, hval⟩ :=
    b52_three_term_locally_affine (fun x ↦ p x / f x) hU hg k C hsum b t hb ht hbt
  let q : E → ℂ := fun x ↦ p x - (L x + d) * f x
  have hq : Differentiable ℂ q := hp.sub ((L.differentiable.add_const d).mul hf)
  have hq0 : q = 0 := by
    by_contra hn
    obtain ⟨x, hx, hxW⟩ := (b52_dense_nonzero hq hn).exists_mem_open hW hWn
    apply hx
    exact sub_eq_zero.mpr ((div_eq_iff (hWU hxW)).mp (hval x hxW))
  refine ⟨L, d, fun x ↦ sub_eq_zero.mp ?_⟩
  exact congrFun hq0 x

theorem b52_differentiable_directional_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {f : E → ℂ}
    (hf : Differentiable ℂ f) (v : E) :
    Differentiable ℂ (fun x ↦ fderiv ℂ f x v) := by
  intro x
  have ha := AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn
    isOpen_univ hf.differentiableOn x (Set.mem_univ x)
  have hc : ContDiffAt ℂ 2 f x := ha.contDiffAt
  have hd := (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact hd.clm_apply (differentiableAt_const v)

theorem b52_logderiv_translated_triple {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (hf : Differentiable ℂ f) (a b c z v : E)
    (ha : f (z + a) ≠ 0) (hb : f (z + b) ≠ 0) (hc : f (z + c) ≠ 0) :
    fderiv ℂ (fun x ↦ f (x + a) * f (x + b) * f (x + c)) z v /
      (f (z + a) * f (z + b) * f (z + c)) =
    fderiv ℂ f (z + a) v / f (z + a) + fderiv ℂ f (z + b) v / f (z + b) +
      fderiv ℂ f (z + c) v / f (z + c) := by
  have hfa := (hf (z + a)).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const a)
  have hfb := (hf (z + b)).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const b)
  have hfc := (hf (z + c)).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const c)
  have he := congrArg (fun A : E →L[ℂ] ℂ ↦ A v) ((hfa.mul hfb).mul hfc).fderiv
  have hd : fderiv ℂ (fun x ↦ f (x + a) * f (x + b) * f (x + c)) z v =
      f (z + c) * (f (z + b) * fderiv ℂ f (z + a) v +
        f (z + a) * fderiv ℂ f (z + b) v) +
      f (z + a) * f (z + b) * fderiv ℂ f (z + c) v := by
    simpa only [Function.comp_def, id_eq, Pi.mul_def, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, mul_add, add_mul,
      mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm] using he
  rw [hd]
  field_simp
  <;> ring

end HodgeLean.Foundations.Program
