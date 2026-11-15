import HodgeLean.Foundations.HodgeGroupAlgebraicGk
import HodgeLean.Foundations.MatrixAlgGroupLieCartier
import HodgeLean.Foundations.CMLieBlocksProofs
import HodgeLean.Foundations.EQWCore
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Helpers for `G_k` (Track G2): the Lie algebra

`g1_lieOfSet (g2_gkGroup b E R J d)` is computed in matrix form.

* Upper bound: the polynomials `x M - M x`, `xᵀ Ω x - Ω`, `det x - 1` and
  `det (x P + 1 - P) - 1` vanish on `G_k`; their differentials at `1` are `Y M - M Y`,
  `Yᵀ Ω + Ω Y`, `tr Y` and `tr (Y P)`.
* Lower bound: for `Y` in the matrix form of `gkLie ⊗ ℂ`, the curve `t ↦ exp (t Y)` lies in
  `G_k`, and the derivative at `0` of a polynomial along it is its differential at `1`.

Both differentials are computed with a chain rule for polynomials along differentiable curves.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations

open MvPolynomial
open scoped TensorProduct

/-! ## A chain rule for polynomials along curves -/

theorem g2k_hasDerivAt_eval {σ : Type*} [Fintype σ] [DecidableEq σ] (c : ℂ → σ → ℂ)
    (c' : σ → ℂ) (t₀ : ℂ) (hc : ∀ i, HasDerivAt (fun t => c t i) (c' i) t₀)
    (f : MvPolynomial σ ℂ) :
    HasDerivAt (fun t => eval (c t) f) (∑ i, eval (c t₀) (pderiv i f) * c' i) t₀ := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa [pderiv_C] using hasDerivAt_const t₀ a
  | add p q hp hq =>
    convert hp.add hq using 1
    · funext t
      simp only [Pi.add_apply, map_add]
    · simp only [map_add, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have h := hp.mul (hc i)
    convert h using 1
    · funext t
      simp
    · simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X]
      simp only [Pi.single_apply, apply_ite (eval (c t₀)), map_one, map_zero, mul_add, add_mul,
        Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_mul]
      rw [add_comm]
      congr 1
      exact Finset.sum_congr rfl fun x _ => by ring

variable {n : ℕ}

/-- Along a matrix curve through `1` with velocity `Y`, the derivative of a polynomial is its
differential at `1`. -/
theorem g2k_hasDerivAt_differential (γ : ℂ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (t₀ : ℂ) (h₀ : γ t₀ = 1) (hγ : ∀ i j, HasDerivAt (fun t => γ t i j) (Y i j) t₀)
    (f : MvPolynomial (Fin n × Fin n) ℂ) :
    HasDerivAt (fun t => eval (fun ij => γ t ij.1 ij.2) f) (g1_differential f Y) t₀ := by
  have h := g2k_hasDerivAt_eval (fun t ij => γ t ij.1 ij.2) (fun ij => Y ij.1 ij.2) t₀
    (fun ij => hγ ij.1 ij.2) f
  have hc : (fun ij : Fin n × Fin n => γ t₀ ij.1 ij.2) =
      g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) ℂ) := by
    funext ij
    rw [h₀]
    rfl
  rw [hc] at h
  rw [g1_differential_apply_dir]
  simpa [mul_comm] using h

/-- The line `t ↦ 1 + t Y`. -/
theorem g2k_hasDerivAt_line (Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℂ => (1 + t • Y) i j) (Y i j) 0 := by
  simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (Y i j)).const_add
    ((1 : Matrix (Fin n) (Fin n) ℂ) i j)

/-- The differential at `1` of a polynomial, read off on the line `1 + t Y`. -/
theorem g2k_differential_eq_of_line (f : MvPolynomial (Fin n × Fin n) ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) {D : ℂ}
    (h : HasDerivAt (fun t : ℂ => eval (fun ij => (1 + t • Y) ij.1 ij.2) f) D 0) :
    g1_differential f Y = D :=
  (g2k_hasDerivAt_differential (fun t => 1 + t • Y) Y 0 (by simp)
    (g2k_hasDerivAt_line Y) f).unique h

/-- The differential of `det` at `1` is the trace. -/
theorem g2k_hasDerivAt_det_line (Z : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℂ => (1 + t • Z).det) Z.trace 0 := by
  have h := (Matrix.det_one_add_X_smul Z)
  have hf : (fun t : ℂ => (1 + t • Z).det) =
      fun t => (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • Z.map Polynomial.C)).eval t := by
    funext t
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j <;>
      simp only [Matrix.one_apply, hij, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.add_apply, Matrix.smul_apply, Polynomial.coe_evalRingHom, Polynomial.eval_add,
        Polynomial.eval_smul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_zero, smul_eq_mul, ite_true, ite_false, Polynomial.eval_mul]
  rw [hf]
  convert Polynomial.hasDerivAt _ (0 : ℂ) using 1
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
    Matrix.coeff_det_one_add_X_smul_one]
  simp

/-- A multiplicative function with zero derivative at `0` and value `1` there is `1`. -/
theorem g2k_eq_one_of_mul (D : ℂ → ℂ) (hmul : ∀ s t, D (s + t) = D s * D t) (h0 : D 0 = 1)
    (hd : HasDerivAt D 0 0) (t : ℂ) : D t = 1 := by
  have hder : ∀ s, HasDerivAt D 0 s := by
    intro s
    have hfun : D = fun t => D s * D (t - s) := funext fun t => by rw [← hmul, add_sub_cancel]
    rw [hfun]
    have h1 : HasDerivAt D 0 (s - s) := by rw [sub_self]; exact hd
    simpa using (h1.comp_sub_const s s).const_mul (D s)
  have := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
    (fun s => (hder s).deriv) t 0
  rw [this, h0]

/-! ## The upper bound -/

theorem g2k_eval_map (x : Fin n × Fin n → ℂ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    eval x (MvPolynomial.map (algebraMap ℚ ℂ) f) = MvPolynomial.aeval x f := by
  rw [eval_map, aeval_def]

theorem g2k_mat_line (Y : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    g2k_mat (fun ij => (1 + t • Y) ij.1 ij.2) = 1 + t • Y := by
  ext i j
  rfl

theorem g2k_eval_mapMatrix_varMatrix (x : Fin n × Fin n → ℂ) :
    (eval x).mapMatrix (g1_varMatrix ℂ n) = g2k_mat x := by
  ext i j
  simp [g1_varMatrix, g2k_mat]

/-- `det (x P + 1 - P) - 1`, a complex polynomial vanishing on `G_k`. -/
def g2k_detPlusPoly (P : Matrix (Fin n) (Fin n) ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  (g1_varMatrix ℂ n * P.map C + (1 - P).map C).det - 1

theorem g2k_eval_detPlusPoly (P : Matrix (Fin n) (Fin n) ℂ) (x : Fin n × Fin n → ℂ) :
    eval x (g2k_detPlusPoly P) = (g2k_mat x * P + (1 - P)).det - 1 := by
  have hC : ∀ M : Matrix (Fin n) (Fin n) ℂ, (eval x).mapMatrix (M.map C) = M := fun M => by
    ext i j
    simp
  rw [g2k_detPlusPoly, map_sub, map_one, RingHom.map_det, map_add, map_mul, hC, hC,
    g2k_eval_mapMatrix_varMatrix]

theorem g2k_hasDerivAt_mul_add_sq (a c : ℂ) :
    HasDerivAt (fun t : ℂ => t * a + t ^ 2 * c) a 0 := by
  simpa using ((hasDerivAt_id (0 : ℂ)).mul_const a).fun_add
    ((hasDerivAt_pow 2 (0 : ℂ)).mul_const c)

section Upper

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (b : Module.Basis (Fin n) ℚ V) (E : LinearMap.BilinForm ℚ V)
  (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V) (d : ℚ)

/-- The matrix form of the complexification of `gkLie E R J`. -/
def g2k_LieCond (Y : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ r ∈ R, Y * (LinearMap.toMatrix b b r).map (algebraMap ℚ ℂ) =
      (LinearMap.toMatrix b b r).map (algebraMap ℚ ℂ) * Y) ∧
    Y * g2k_Jm b J = g2k_Jm b J * Y ∧
    Matrix.transpose Y * (LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ) +
        (LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ) * Y = 0 ∧
    Y.trace = 0 ∧ (g2k_Jm b J * Y).trace = 0

/-- The differential of a commutation equation. -/
theorem g2k_differential_commEquations (M : Matrix (Fin n) (Fin n) ℚ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    g1_differential (MvPolynomial.map (algebraMap ℚ ℂ) (g2_commEquations M i j)) Y =
      (Y * M.map (algebraMap ℚ ℂ) - M.map (algebraMap ℚ ℂ) * Y) i j := by
  refine g2k_differential_eq_of_line _ Y ?_
  have hf : (fun t : ℂ => eval (fun ij => (1 + t • Y) ij.1 ij.2)
      (MvPolynomial.map (algebraMap ℚ ℂ) (g2_commEquations M i j))) =
      fun t => t * (Y * M.map (algebraMap ℚ ℂ) - M.map (algebraMap ℚ ℂ) * Y) i j := by
    funext t
    rw [g2k_eval_map, g2k_aeval_commEquations, g2k_mat_line]
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hf]
  simpa using (hasDerivAt_id (0 : ℂ)).mul_const
    ((Y * M.map (algebraMap ℚ ℂ) - M.map (algebraMap ℚ ℂ) * Y) i j)

/-- The differential of an isometry equation. -/
theorem g2k_differential_isometryEquations (M : Matrix (Fin n) (Fin n) ℚ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    g1_differential (MvPolynomial.map (algebraMap ℚ ℂ) (g1_isometryEquations M i j)) Y =
      (Matrix.transpose Y * M.map (algebraMap ℚ ℂ) + M.map (algebraMap ℚ ℂ) * Y) i j := by
  refine g2k_differential_eq_of_line _ Y ?_
  set Ω := M.map (algebraMap ℚ ℂ)
  have hm : ∀ t : ℂ, Matrix.transpose (1 + t • Y) * Ω * (1 + t • Y) - Ω =
      t • (Matrix.transpose Y * Ω + Ω * Y) + t ^ 2 • (Matrix.transpose Y * Ω * Y) := by
    intro t
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, add_mul, mul_add,
      one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, pow_two]
    abel
  have hf : (fun t : ℂ => eval (fun ij => (1 + t • Y) ij.1 ij.2)
      (MvPolynomial.map (algebraMap ℚ ℂ) (g1_isometryEquations M i j))) =
      fun t => t * (Matrix.transpose Y * Ω + Ω * Y) i j + t ^ 2 * (Matrix.transpose Y * Ω * Y) i j := by
    funext t
    rw [g2k_eval_map, g2k_aeval_isometryEquations, g2k_mat_line, hm]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hf]
  exact g2k_hasDerivAt_mul_add_sq _ _

theorem g2k_differential_det_sub_one (Y : Matrix (Fin n) (Fin n) ℂ) :
    g1_differential (MvPolynomial.map (algebraMap ℚ ℂ) ((g1_varMatrix ℚ n).det - 1)) Y =
      Y.trace := by
  refine g2k_differential_eq_of_line _ Y ?_
  have hf : (fun t : ℂ => eval (fun ij => (1 + t • Y) ij.1 ij.2)
      (MvPolynomial.map (algebraMap ℚ ℂ) ((g1_varMatrix ℚ n).det - 1))) =
      fun t => (1 + t • Y).det - 1 := by
    funext t
    rw [g2k_eval_map, g2k_aeval_det_sub_one, g2k_mat_line]
  rw [hf]
  exact (g2k_hasDerivAt_det_line Y).sub_const 1

theorem g2k_differential_detPlusPoly (P Y : Matrix (Fin n) (Fin n) ℂ) :
    g1_differential (g2k_detPlusPoly P) Y = (Y * P).trace := by
  refine g2k_differential_eq_of_line _ Y ?_
  have hf : (fun t : ℂ => eval (fun ij => (1 + t • Y) ij.1 ij.2) (g2k_detPlusPoly P)) =
      fun t => (1 + t • (Y * P)).det - 1 := by
    funext t
    rw [g2k_eval_detPlusPoly, g2k_mat_line]
    congr 2
    simp only [add_mul, one_mul, Matrix.smul_mul]
    abel
  rw [hf]
  exact (g2k_hasDerivAt_det_line (Y * P)).sub_const 1

theorem g2k_c_ne_zero {d : ℚ} (hd : 0 < d) : g2k_c d ≠ 0 := by
  have h := g2k_c_sq hd
  intro h0
  rw [h0] at h
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp at h
  norm_num at h

/-- **Upper bound for `Lie(G_k)`.** -/
theorem g2k_lieCond_of_mem {d : ℚ} (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V))
    (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y ∈ g1_lieOfSet (g2_gkGroup b E R J d)) :
    g2k_LieCond b E R J Y := by
  have hvan : ∀ f, (∀ g ∈ g2_gkGroup b E R J d, eval (g1_coords g) f = 0) →
      g1_differential f Y = 0 := fun f hf =>
    g1_mem_lieOfSet_iff.mp hY f (g1_mem_vanishingIdealSet_iff.mpr hf)
  have hrat : ∀ f ∈ g2_gkEquations b E R J d,
      g1_differential (MvPolynomial.map (algebraMap ℚ ℂ) f) Y = 0 := fun f hf =>
    hvan _ fun g hg => by rw [g2k_eval_map]; exact hg f hf
  have hentries : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (∀ i j, (A - B) i j = 0) → A = B :=
    fun A B h => g2k_matrix_eq_iff_entries.mpr h
  refine ⟨fun r hr => hentries _ _ fun i j => ?_, hentries _ _ fun i j => ?_, ?_, ?_, ?_⟩
  · rw [← g2k_differential_commEquations]
    exact hrat _ (Or.inl (Or.inl (Or.inl ⟨r, hr, i, j, rfl⟩)))
  · rw [g2k_Jm, ← g2k_differential_commEquations]
    exact hrat _ (Or.inl (Or.inl (Or.inr ⟨i, j, rfl⟩)))
  · ext i j
    rw [← g2k_differential_isometryEquations]
    exact hrat _ (Or.inl (Or.inr ⟨i, j, rfl⟩))
  · rw [← g2k_differential_det_sub_one]
    exact hrat _ (Or.inr (Or.inl rfl))
  · have htr : Y.trace = 0 := by
      rw [← g2k_differential_det_sub_one]
      exact hrat _ (Or.inr (Or.inl rfl))
    have hplus : (Y * g2k_P b J d).trace = 0 := by
      rw [← g2k_differential_detPlusPoly]
      refine hvan _ fun g hg => ?_
      rw [g2k_eval_detPlusPoly, g2k_mat_coords, ((g2k_mem_gkGroup_iff b E R J hd hJ g).mp hg).2.2.2.1,
        sub_self]
    rw [g2k_P_eq, mul_add, Matrix.mul_smul, Matrix.mul_smul, mul_one, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul, htr, smul_zero, zero_add, smul_eq_mul] at hplus
    rw [Matrix.trace_mul_comm]
    have hc : -g2k_c d / 2 ≠ 0 := by
      have := g2k_c_ne_zero hd
      intro h
      apply this
      linear_combination -2 * h
    exact (mul_eq_zero.mp hplus).resolve_left hc

end Upper

/-! ## The lower bound: the exponential curve -/

section Lower

open NormedSpace

set_option backward.isDefEq.respectTransparency false in
/-- Entries of `exp (t Y) A` are differentiable in `t`. -/
theorem g2k_hasDerivAt_exp_mul (Y A : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) (i j : Fin n) :
    HasDerivAt (fun s : ℂ => (exp (s • Y) * A) i j) ((exp (t • Y) * Y * A) i j) t := by
  open scoped Matrix.Norms.Operator in
  have h : HasDerivAt (fun u : ℂ => exp (u • Y)) (exp (t • Y) * Y) t :=
    hasDerivAt_exp_smul_const Y t
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    (Matrix.entryLinearMap ℂ ℂ i j) ∘ₗ (LinearMap.mulRight ℂ A)
  open scoped Matrix.Norms.Operator in
  have := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t h
  exact this

/-- `exp (t Y)` as an invertible matrix. -/
def g2k_expGL (Y : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) : Matrix.GeneralLinearGroup (Fin n) ℂ :=
  (Matrix.isUnit_exp (t • Y)).unit

theorem g2k_coe_expGL (Y : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    (g2k_expGL Y t : Matrix (Fin n) (Fin n) ℂ) = exp (t • Y) :=
  IsUnit.unit_spec _

theorem g2k_exp_add (Y : Matrix (Fin n) (Fin n) ℂ) (s t : ℂ) :
    exp ((s + t) • Y) = exp (s • Y) * exp (t • Y) := by
  rw [add_smul, Matrix.exp_add_of_commute]
  exact ((Commute.refl Y).smul_left s).smul_right t

set_option backward.isDefEq.respectTransparency false in
theorem g2k_exp_commute (Y M : Matrix (Fin n) (Fin n) ℂ) (h : Y * M = M * Y) (t : ℂ) :
    exp (t • Y) * M = M * exp (t • Y) := by
  open scoped Matrix.Norms.Operator in
  exact (Commute.exp_left ((show Commute Y M from h).smul_left t)).eq

set_option backward.isDefEq.respectTransparency false in
theorem g2k_exp_isometry (Y Ω : Matrix (Fin n) (Fin n) ℂ)
    (h : Matrix.transpose Y * Ω + Ω * Y = 0) (t : ℂ) :
    Matrix.transpose (exp (t • Y)) * Ω * exp (t • Y) = Ω := by
  have hs : SemiconjBy Ω (-(t • Y)) (t • Matrix.transpose Y) := by
    rw [SemiconjBy, mul_neg, Matrix.mul_smul, Matrix.smul_mul, ← neg_smul]
    rw [add_eq_zero_iff_eq_neg] at h
    rw [h, neg_smul, smul_neg]
  have he : Ω * exp (-(t • Y)) = exp (t • Matrix.transpose Y) * Ω := by
    open scoped Matrix.Norms.Operator in
    exact (SemiconjBy.exp_right hs).eq
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, ← he, mul_assoc, ← Matrix.exp_add_of_commute,
    neg_add_cancel, exp_zero, mul_one]
  exact (Commute.refl _).neg_left

/-- The determinant of `exp (t Y)` on the range of an idempotent `e` commuting with `Y`, with
`tr (Y e) = 0`, is `1`. -/
theorem g2k_det_exp_proj (Y e : Matrix (Fin n) (Fin n) ℂ) (he : e * e = e) (hYe : Y * e = e * Y)
    (htr : (Y * e).trace = 0) (t : ℂ) : (exp (t • Y) * e + (1 - e)).det = 1 := by
  let D : ℂ → ℂ := fun s => (exp (s • Y) * e + (1 - e)).det
  have hmul : ∀ s s', D (s + s') = D s * D s' := by
    intro s s'
    simp only [D]
    rw [← Matrix.det_mul, g2k_proj_mul_proj _ _ _ he (g2k_exp_commute Y e hYe s'), g2k_exp_add]
  have h0 : D 0 = 1 := by simp [D]
  have hd : HasDerivAt D 0 0 := by
    have hγ : ∀ i j, HasDerivAt (fun s : ℂ => (exp (s • Y) * e + (1 - e)) i j) ((Y * e) i j) 0 := by
      intro i j
      have := (g2k_hasDerivAt_exp_mul Y e 0 i j).add_const ((1 - e) i j)
      simpa using this
    have h1 := g2k_hasDerivAt_differential (fun s : ℂ => exp (s • Y) * e + (1 - e)) (Y * e) 0
      (by simp) hγ (g1_varMatrix ℂ n).det
    have h2 : g1_differential (g1_varMatrix ℂ n).det (Y * e) = (Y * e).trace := by
      refine g2k_differential_eq_of_line _ _ ?_
      have hf : (fun t : ℂ => eval (fun ij => (1 + t • (Y * e)) ij.1 ij.2)
          (g1_varMatrix ℂ n).det) = fun t => (1 + t • (Y * e)).det := by
        funext t
        rw [RingHom.map_det, g2k_eval_mapMatrix_varMatrix, g2k_mat_line]
      rw [hf]
      exact g2k_hasDerivAt_det_line _
    have hf : (fun s : ℂ => eval (fun ij => (exp (s • Y) * e + (1 - e)) ij.1 ij.2)
        (g1_varMatrix ℂ n).det) = D := by
      funext s
      rw [RingHom.map_det, g2k_eval_mapMatrix_varMatrix]
      rfl
    rw [hf, h2, htr] at h1
    exact h1
  exact g2k_eq_one_of_mul D hmul h0 hd t

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (b : Module.Basis (Fin n) ℚ V) (E : LinearMap.BilinForm ℚ V)
  (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V)

/-- The exponential curve of an element of the matrix form of `gkLie ⊗ ℂ` lies in `G_k`. -/
theorem g2k_expGL_mem {d : ℚ} (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V))
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : g2k_LieCond b E R J Y) (t : ℂ) :
    g2k_expGL Y t ∈ g2_gkGroup b E R J d := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hY
  have hP := g2k_P_mul_self b J hd hJ
  have hQ := g2k_one_sub_P_mul_self b J hd hJ
  have hYP := g2k_commute_P b J (d := d) h2
  have hYQ := g2k_commute_one_sub_P b J (d := d) h2
  have htrP : (Y * g2k_P b J d).trace = 0 := by
    rw [g2k_P_eq, mul_add, Matrix.mul_smul, Matrix.mul_smul, mul_one, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul, h4, Matrix.trace_mul_comm, h5]
    simp
  have htrQ : (Y * (1 - g2k_P b J d)).trace = 0 := by
    rw [mul_sub, mul_one, Matrix.trace_sub, h4, htrP, sub_zero]
  rw [g2k_mem_gkGroup_iff b E R J hd hJ, g2k_coe_expGL]
  refine ⟨fun r hr => g2k_exp_commute Y _ (h1 r hr) t, g2k_exp_commute Y _ h2 t,
    g2k_exp_isometry Y _ h3 t, g2k_det_exp_proj Y _ hP hYP htrP t, ?_⟩
  have := g2k_det_exp_proj Y _ hQ hYQ htrQ t
  rwa [sub_sub_cancel] at this

/-- **Lower bound for `Lie(G_k)`.** -/
theorem g2k_mem_of_lieCond {d : ℚ} (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V))
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : g2k_LieCond b E R J Y) :
    Y ∈ g1_lieOfSet (g2_gkGroup b E R J d) := by
  refine g1_mem_lieOfSet_iff.mpr fun f hf => ?_
  have hγ : ∀ i j, HasDerivAt (fun s : ℂ => exp (s • Y) i j) (Y i j) 0 := by
    intro i j
    simpa using g2k_hasDerivAt_exp_mul Y 1 0 i j
  have h1 := g2k_hasDerivAt_differential (fun s : ℂ => exp (s • Y)) Y 0 (by simp) hγ f
  have hzero : (fun s : ℂ => eval (fun ij => exp (s • Y) ij.1 ij.2) f) = fun _ => 0 := by
    funext s
    have := g1_mem_vanishingIdealSet_iff.mp hf _ (g2k_expGL_mem b E R J hd hJ hY s)
    rw [← this]
    congr 1
  rw [hzero] at h1
  exact h1.unique (hasDerivAt_const 0 0)

/-- **`Lie(G_k)` in matrix form.** -/
theorem g2k_lieOfSet_gkGroup {d : ℚ} (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V))
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y ∈ g1_lieOfSet (g2_gkGroup b E R J d) ↔ g2k_LieCond b E R J Y :=
  ⟨g2k_lieCond_of_mem b E R J hd hJ Y, g2k_mem_of_lieCond b E R J hd hJ⟩

end Lower

/-! ## The complexification of `gkLie` in matrix form -/

section Span

attribute [local instance 100] LieRing.ofAssociativeRing

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- `gkLie E R J` is cut out by rational linear equations, so its complexification is cut out by
the same equations over `ℂ` (the case `R = ι(L)` with `J ∈ R` is
`spec_a2b_mem_complexSpan_gkLie_iff`). -/
theorem g2k_mem_complexSpan_gkLie_iff [FiniteDimensional ℚ V] (E : LinearMap.BilinForm ℚ V)
    (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V) (X : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    X ∈ complexSpan (gkLie E R J).toSubmodule ↔
      (∀ r ∈ R, X * r.baseChange ℂ = r.baseChange ℂ * X) ∧
      X * J.baseChange ℂ = J.baseChange ℂ * X ∧
      (∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) ∧
      LinearMap.trace ℂ (ℂ ⊗[ℚ] V) X = 0 ∧
      LinearMap.trace ℂ (ℂ ⊗[ℚ] V) (J.baseChange ℂ * X) = 0 := by
  let R' : Submodule ℚ (Module.End ℚ V) := Subalgebra.toSubmodule R
  let bR := Module.finBasis ℚ R'
  have hspan : ∀ {P : Module.End ℚ V → Prop}, P 0 → (∀ S T, P S → P T → P (S + T)) →
      (∀ (q : ℚ) S, P S → P (q • S)) → (∀ i, P (bR i)) → ∀ r ∈ R', P r := by
    intro P h0 hadd hsmul hb r hr
    have hr' : (⟨r, hr⟩ : R') ∈ Submodule.span ℚ (Set.range bR) := by rw [bR.span_eq]; trivial
    exact Submodule.span_induction (p := fun (s : R') _ => P s)
      (by rintro _ ⟨i, rfl⟩; exact hb i) h0 (fun s t _ _ hs ht => hadd s t hs ht)
      (fun q s _ hs => hsmul q s hs) hr'
  have hgk : (gkLie E R J).toSubmodule = (weilSU E J).toSubmodule ⊓
      Finset.univ.inf fun i => LinearMap.ker (a2bCommMap ((bR i : R') : Module.End ℚ V)) := by
    ext Y
    simp only [LieSubalgebra.mem_toSubmodule, Submodule.mem_inf, Submodule.mem_finsetInf,
      Finset.mem_univ, true_imp_iff, a2b_mem_ker_commMap]
    refine and_congr_right fun _ => ⟨fun h i => h _ (bR i).2, fun h r hr => ?_⟩
    exact hspan (P := fun r => Y * r = r * Y) (by simp)
      (fun S T hS hT => by rw [mul_add, add_mul, hS, hT])
      (fun q S hS => by rw [mul_smul_comm, smul_mul_assoc, hS]) h r hr
  rw [hgk, complexSpan_inf, a2b_complexSpan_finsetInf, Submodule.mem_inf,
    spec_eqw_mem_complexSpan_weilSU_iff, Submodule.mem_finsetInf]
  simp only [Finset.mem_univ, true_imp_iff, a2b_complexSpan_ker_commMap, a2b_mem_ker_commMap]
  constructor
  · rintro ⟨⟨h2, h3, h4, h5⟩, h1⟩
    refine ⟨fun r hr => ?_, h2, h3, h4, h5⟩
    refine hspan (P := fun r => X * r.baseChange ℂ = r.baseChange ℂ * X) (by simp)
      (fun S T hS hT => by rw [LinearMap.baseChange_add, mul_add, add_mul, hS, hT])
      (fun q S hS => ?_) h1 r hr
    rw [LinearMap.baseChange_smul, mul_smul_comm, smul_mul_assoc, hS]
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨h2, h3, h4, h5⟩, fun i => h1 _ (bR i).2⟩

variable {n : ℕ} (b : Module.Basis (Fin n) ℚ V)

theorem g2k_toMatrix_baseChange_bilin (E : LinearMap.BilinForm ℚ V) :
    LinearMap.BilinForm.toMatrix (Algebra.TensorProduct.basis ℂ b) (E.baseChange ℂ) =
      (LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ) := by
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply, Algebra.TensorProduct.basis_apply,
    Algebra.algebraMap_eq_smul_one]

/-- **The complexified `gkLie`, in matrix form.** -/
theorem g2k_mem_map_complexSpan_gkLie_iff (E : LinearMap.BilinForm ℚ V)
    (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y ∈ (complexSpan (gkLie E R J).toSubmodule).map
        (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
          (Algebra.TensorProduct.basis ℂ b)).toLinearMap ↔
      g2k_LieCond b E R J Y := by
  have := Module.Finite.of_basis b
  set c := Algebra.TensorProduct.basis ℂ b
  set φ := LinearMap.toMatrix c c
  rw [Submodule.mem_map_equiv, g2k_mem_complexSpan_gkLie_iff]
  set X := φ.symm Y
  have hX : φ X = Y := φ.apply_symm_apply Y
  have hmul : ∀ (f : Module.End ℚ V),
      (X * f.baseChange ℂ = f.baseChange ℂ * X ↔
        Y * (LinearMap.toMatrix b b f).map (algebraMap ℚ ℂ) =
          (LinearMap.toMatrix b b f).map (algebraMap ℚ ℂ) * Y) := by
    intro f
    rw [← φ.injective.eq_iff, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.toMatrix_comp c c c, LinearMap.toMatrix_comp c c c, hX,
      LinearMap.toMatrix_baseChange]
  have hskew : (∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) ↔
      Matrix.transpose Y * (LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ) +
        (LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ) * Y = 0 := by
    have h1 : (∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) ↔
        (E.baseChange ℂ).compLeft X = -(E.baseChange ℂ).compRight X := by
      constructor
      · intro h
        ext x y
        simp [h]
      · intro h x y
        have := LinearMap.congr_fun₂ h x y
        simpa using this
    rw [h1, ← (LinearMap.BilinForm.toMatrix c).injective.eq_iff, map_neg,
      LinearMap.BilinForm.toMatrix_compLeft, LinearMap.BilinForm.toMatrix_compRight, hX,
      g2k_toMatrix_baseChange_bilin, add_eq_zero_iff_eq_neg]
  have htr1 : LinearMap.trace ℂ (ℂ ⊗[ℚ] V) X = Y.trace := by
    rw [LinearMap.trace_eq_matrix_trace ℂ c, hX]
  have htr2 : LinearMap.trace ℂ (ℂ ⊗[ℚ] V) (J.baseChange ℂ * X) = (g2k_Jm b J * Y).trace := by
    rw [LinearMap.trace_eq_matrix_trace ℂ c, Module.End.mul_eq_comp, LinearMap.toMatrix_comp c c c,
      hX, LinearMap.toMatrix_baseChange, g2k_Jm]
  rw [hskew, htr1, htr2, g2k_LieCond, g2k_Jm]
  exact and_congr (forall₂_congr fun r _ => hmul r) (and_congr (hmul J) Iff.rfl)

end Span

end HodgeLean.Foundations
