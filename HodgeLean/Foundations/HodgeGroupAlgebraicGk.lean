import HodgeLean.Foundations.HodgeGroupAlgebraicDefs

/-! # Helpers for `G_k` (Track G2): the `k`-determinant

For `J² = -d`, `d > 0`, the matrix `P = (1 - (i/√d) J)/2` is the projector onto the
`i√d`-eigenspace `V₊` of `J` along `V₋`. For `y` commuting with `J`,
`det (y + s + t J) = det (y + w P) det (y + w̄ (1 - P))` in spirit; we read off the coefficients
through the substitutions `s ↦ w/2`, `t ↦ ∓ (i/√d) w/2` and the leading coefficient of
`det (y + w Q)` for an idempotent `Q` commuting with `y`. The result is
`g2k_aeval_kDetTrace`: `g2_kDetTrace` evaluates to `det(y P + 1 - P) + det(y (1 - P) + P)`.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations

open Polynomial
open scoped TensorProduct

/-! ## Determinants of maps preserving a decomposition -/

/-- The determinant of an endomorphism preserving two complementary subspaces is the product of
the determinants of its restrictions. -/
theorem g2k_det_eq_mul_restrict {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (f : Module.End K M) {p q : Submodule K M} (h : IsCompl p q)
    (hp : ∀ x ∈ p, f x ∈ p) (hq : ∀ x ∈ q, f x ∈ q) :
    LinearMap.det f = LinearMap.det (f.restrict hp) * LinearMap.det (f.restrict hq) := by
  let e := p.prodEquivOfIsCompl q h
  have hf : f = (e : (p × q) →ₗ[K] M) ∘ₗ (LinearMap.prodMap (f.restrict hp) (f.restrict hq)) ∘ₗ
      (e.symm : M →ₗ[K] p × q) := by
    ext x
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective x
    simp [e, Submodule.coe_prodEquivOfIsCompl']
  conv_lhs => rw [hf]
  rw [LinearMap.det_conj, LinearMap.det_prodMap]

/-! ## Ring identities for an idempotent commuting with an element -/

section RingId

variable {A : Type*} [Ring A] (a e : A)

theorem g2k_mul_proj_add [Algebra ℂ A] (w : ℂ) (he : e * e = e) (hae : a * e = e * a) :
    (a * (1 - e) + e) * (a * e + (1 - e) + w • e) = a + w • e := by
  have h1 : ∀ x, e * (a * x) = a * (e * x) := fun x => by rw [← mul_assoc, ← hae, mul_assoc]
  have h2 : ∀ x, e * (e * x) = e * x := fun x => by rw [← mul_assoc, he]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
    mul_assoc, h1, h2, he, ← hae, sub_self, smul_add, smul_zero, zero_add]
  abel

theorem g2k_proj_mul_proj (b : A) (he : e * e = e) (hbe : b * e = e * b) :
    (a * e + (1 - e)) * (b * e + (1 - e)) = a * b * e + (1 - e) := by
  have h1 : ∀ x, e * (b * x) = b * (e * x) := fun x => by rw [← mul_assoc, ← hbe, mul_assoc]
  have h2 : ∀ x, e * (e * x) = e * x := fun x => by rw [← mul_assoc, he]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_assoc, h1, h2, he, ← hbe]
  abel

theorem g2k_proj_mul_compl (he : e * e = e) (hae : a * e = e * a) :
    (a * e + (1 - e)) * (a * (1 - e) + e) = a := by
  have h1 : ∀ x, e * (a * x) = a * (e * x) := fun x => by rw [← mul_assoc, ← hae, mul_assoc]
  have h2 : ∀ x, e * (e * x) = e * x := fun x => by rw [← mul_assoc, he]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, mul_assoc, h1, h2, he, ← hae]
  abel

end RingId

/-- **The leading coefficient of `det (y + w Q)`.** For an idempotent `Q` of trace `r` commuting
with `y`, the coefficient of `w^r` in `det (y + w Q)` is `det (y (1 - Q) + Q)`. -/
theorem g2k_coeff_det_add_X_smul {n : ℕ} (y Q : Matrix (Fin n) (Fin n) ℂ) (hQ : Q * Q = Q)
    (hyQ : y * Q = Q * y) {r : ℕ} (hr : Q.trace = r) :
    (Matrix.det (y.map C + (X : ℂ[X]) • Q.map C)).coeff r = (y * (1 - Q) + Q).det := by
  let φ : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin n → ℂ) := Matrix.toLinAlgEquiv'
  have hφ : ∀ M, LinearMap.det (φ M) = M.det := fun M => LinearMap.det_toLin' M
  set q := φ Q with hqdef
  set yl := φ y with hyl
  have hqq : q * q = q := by rw [hqdef, ← map_mul, hQ]
  have hproj := (LinearMap.isProj_range_iff_isIdempotentElem q).mpr hqq
  have hyq : yl * q = q * yl := by rw [hyl, hqdef, ← map_mul, ← map_mul, hyQ]
  -- `y` preserves the range of `q`
  have hyp : ∀ x ∈ LinearMap.range q, yl x ∈ LinearMap.range q := by
    rintro _ ⟨v, rfl⟩
    exact ⟨yl v, by rw [← Module.End.mul_apply, ← hyq, Module.End.mul_apply]⟩
  have hfin : Module.finrank ℂ (LinearMap.range q) = r := by
    have h1 := hproj.trace
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)),
      LinearMap.toMatrix_eq_toMatrix', show q = Matrix.toLin' Q from rfl,
      LinearMap.toMatrix'_toLin', hr] at h1
    exact_mod_cast h1.symm
  let yp := yl.restrict hyp
  have hF : Matrix.det (y.map C + (X : ℂ[X]) • Q.map C) =
      C (y * (1 - Q) + Q).det * LinearMap.charpoly (-yp) := by
    refine Polynomial.funext fun w => ?_
    rw [eval_mul, eval_C, LinearMap.eval_charpoly]
    have hev : (Matrix.det (y.map C + (X : ℂ[X]) • Q.map C)).eval w = (y + w • Q).det := by
      rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
      congr 1
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
        coe_evalRingHom, eval_add, eval_C, smul_eq_mul, eval_mul, eval_X]
    rw [hev, ← g2k_mul_proj_add y Q w hQ hyQ, Matrix.det_mul]
    congr 1
    set A := φ (y * Q + (1 - Q) + w • Q) with hA
    have hAe : A = yl * q + (1 - q) + w • q := by
      rw [hA, map_add, map_add, map_mul, map_sub, map_one, map_smul]
    have hAp : ∀ x ∈ LinearMap.range q, A x ∈ LinearMap.range q := by
      rintro _ ⟨v, rfl⟩
      rw [hAe]
      refine ⟨yl (q v) + w • q v, ?_⟩
      simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul]
      rw [← Module.End.mul_apply q q, hqq, ← Module.End.mul_apply q yl, ← hyq,
        Module.End.mul_apply, ← Module.End.mul_apply q q, hqq]
      abel
    have hAq : ∀ x ∈ LinearMap.ker q, A x ∈ LinearMap.ker q := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hAe]
      simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul, map_sub, hx, map_zero,
        smul_zero, add_zero, sub_zero]
    rw [← hφ, g2k_det_eq_mul_restrict A hproj.isCompl hAp hAq]
    have h1 : A.restrict hAq = LinearMap.id := by
      ext ⟨x, hx⟩
      rw [LinearMap.mem_ker] at hx
      simp only [LinearMap.restrict_apply, LinearMap.id_coe, id_eq, hAe, LinearMap.add_apply,
        LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply, hx,
        map_zero, smul_zero, add_zero, zero_add, sub_zero]
    have h2 : A.restrict hAp = algebraMap ℂ (Module.End ℂ (LinearMap.range q)) w - -yp := by
      ext ⟨_, v, rfl⟩
      simp only [LinearMap.restrict_apply, hAe, LinearMap.add_apply, LinearMap.sub_apply,
        Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply,
        Module.algebraMap_end_apply, sub_neg_eq_add, Submodule.coe_add, Submodule.coe_smul, yp]
      rw [← Module.End.mul_apply q q, hqq, sub_self, add_zero, add_comm]
    rw [h1, h2, LinearMap.det_id, mul_one]
  have hmon := LinearMap.charpoly_monic (-yp)
  have hdeg := LinearMap.charpoly_natDegree (-yp)
  rw [hF, coeff_C_mul, ← hfin, ← hdeg, hmon.coeff_natDegree, mul_one]

/-! ## Substituting `s ↦ p w`, `t ↦ q w` -/

/-- The substitution `s ↦ p w`, `t ↦ q w` from `ℂ[s][t]` to `ℂ[w]`. -/
def g2k_subst (p q : ℂ) : ℂ[X][X] →+* ℂ[X] :=
  eval₂RingHom (eval₂RingHom C (C p * X)) (C q * X)

theorem g2k_coeff_eval₂_C_mul_X (p : ℂ) (h : ℂ[X]) (k : ℕ) :
    (h.eval₂ C (C p * X)).coeff k = p ^ k * h.coeff k := by
  induction h using Polynomial.induction_on' with
  | add f g hf hg => rw [eval₂_add, coeff_add, coeff_add, hf, hg, mul_add]
  | monomial m a =>
    rw [eval₂_monomial, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow, coeff_monomial]
    split_ifs with h1 h2 h2
    · subst h1; ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring

/-- The coefficient of `w^m` after the substitution: `Σ_{b ≤ m} q^b p^(m-b) c_{m-b,b}`. -/
theorem g2k_coeff_subst (p q : ℂ) (H : ℂ[X][X]) (m : ℕ) :
    (g2k_subst p q H).coeff m =
      ∑ b ∈ Finset.range (m + 1), q ^ b * p ^ (m - b) * (H.coeff b).coeff (m - b) := by
  induction H using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, coeff_add, hf, hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [coeff_add, coeff_add, mul_add]
  | monomial k h =>
    simp only [g2k_subst, coe_eval₂RingHom, eval₂_monomial, mul_pow, ← C_pow]
    rw [← mul_assoc, coeff_mul_X_pow', coeff_mul_C]
    by_cases hk : k ≤ m
    · rw [if_pos hk, Finset.sum_eq_single k, coeff_monomial, if_pos rfl,
        g2k_coeff_eval₂_C_mul_X]
      · ring
      · intro b _ hb
        rw [coeff_monomial, if_neg (Ne.symm hb), coeff_zero, mul_zero]
      · intro h'
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) h'
    · rw [if_neg hk, Finset.sum_eq_zero]
      intro b hb
      have : k ≠ b := fun h' => hk (h' ▸ Nat.le_of_lt_succ (Finset.mem_range.mp hb))
      rw [coeff_monomial, if_neg this, coeff_zero, mul_zero]

/-- Doubling the even-index terms. -/
theorem g2k_sum_even (f : ℕ → ℂ) (m : ℕ) :
    ∑ b ∈ Finset.range (m + 1), (1 + (-1) ^ b) * f b =
      ∑ j ∈ Finset.range (m / 2 + 1), 2 * f (2 * j) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => norm_num
    | 1, _ => norm_num [Finset.sum_range_succ]
    | k + 2, ih =>
      have h := ih k (by omega)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, h,
        show (k + 2) / 2 + 1 = k / 2 + 1 + 1 by omega,
        Finset.sum_range_succ (fun j => 2 * f (2 * j)) (k / 2 + 1)]
      rcases Nat.even_or_odd k with hk | hk
      · have h1 : (-1 : ℂ) ^ (k + 1) = -1 := by rw [pow_succ, hk.neg_one_pow]; ring
        have h2 : (-1 : ℂ) ^ (k + 2) = 1 := by rw [pow_add, hk.neg_one_pow]; norm_num
        have h3 : 2 * (k / 2 + 1) = k + 2 := by obtain ⟨l, rfl⟩ := hk; omega
        rw [h1, h2, h3]
        ring
      · have h1 : (-1 : ℂ) ^ (k + 1) = 1 := by rw [pow_succ, hk.neg_one_pow]; ring
        have h2 : (-1 : ℂ) ^ (k + 2) = -1 := by rw [pow_add, hk.neg_one_pow]; norm_num
        have h3 : 2 * (k / 2 + 1) = k + 1 := by obtain ⟨l, rfl⟩ := hk; omega
        rw [h1, h2, h3]
        ring

/-! ## The projector onto `V₊` -/

/-- Products of matrices of the form `a + b J` with `J² = -d`. -/
theorem g2k_lin_mul {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) {d : ℂ} (hJ : J * J = (-d) • 1)
    (a b a' b' : ℂ) :
    (a • 1 + b • J) * (a' • 1 + b' • J) = (a * a' - b * b' * d) • 1 + (a * b' + a' * b) • J := by
  simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hJ, smul_smul]
  module

section Proj

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ}

/-- The matrix of `J` in the basis `b`, with complex entries. -/
def g2k_Jm (b : Module.Basis (Fin n) ℚ V) (J : Module.End ℚ V) : Matrix (Fin n) (Fin n) ℂ :=
  (LinearMap.toMatrix b b J).map (algebraMap ℚ ℂ)

/-- The scalar `i/√d`. -/
def g2k_c (d : ℚ) : ℂ := Complex.I / ((Real.sqrt d : ℝ) : ℂ)

/-- The projector `P = (1 - (i/√d) J)/2` onto the `i√d`-eigenspace of `J`. -/
def g2k_P (b : Module.Basis (Fin n) ℚ V) (J : Module.End ℚ V) (d : ℚ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (1 - g2k_c d • g2k_Jm b J)

theorem g2k_c_sq {d : ℚ} (hd : 0 < d) : g2k_c d ^ 2 = -1 / (d : ℂ) := by
  have h : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by exact_mod_cast hd.le)]
    simp
  rw [g2k_c, div_pow, Complex.I_sq, h]

theorem g2k_c_sq_mul {d : ℚ} (hd : 0 < d) : g2k_c d ^ 2 * (d : ℂ) = -1 := by
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [g2k_c_sq hd]
  field_simp

variable (b : Module.Basis (Fin n) ℚ V) (J : Module.End ℚ V) {d : ℚ}

theorem g2k_Jm_mul_self (hJ : J * J = (-d) • (1 : Module.End ℚ V)) :
    g2k_Jm b J * g2k_Jm b J = (-(d : ℂ)) • 1 := by
  rw [g2k_Jm, ← Matrix.map_mul, ← LinearMap.toMatrix_mul, hJ, map_smul, LinearMap.toMatrix_one]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem g2k_P_eq : g2k_P b J d = (1 / 2 : ℂ) • 1 + (-g2k_c d / 2) • g2k_Jm b J := by
  rw [g2k_P]
  module

theorem g2k_one_sub_P_eq : 1 - g2k_P b J d = (1 / 2 : ℂ) • 1 + (g2k_c d / 2) • g2k_Jm b J := by
  rw [g2k_P]
  module

theorem g2k_P_mul_self (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V)) :
    g2k_P b J d * g2k_P b J d = g2k_P b J d := by
  rw [g2k_P_eq, g2k_lin_mul _ (g2k_Jm_mul_self b J hJ)]
  have h := g2k_c_sq_mul hd
  congr 2
  · linear_combination (-1 / 4 : ℂ) * h
  · ring

theorem g2k_one_sub_P_mul_self (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V)) :
    (1 - g2k_P b J d) * (1 - g2k_P b J d) = 1 - g2k_P b J d := by
  rw [mul_sub, sub_mul, sub_mul, g2k_P_mul_self b J hd hJ]
  simp

theorem g2k_commute_P {y : Matrix (Fin n) (Fin n) ℂ} (hy : y * g2k_Jm b J = g2k_Jm b J * y) :
    y * g2k_P b J d = g2k_P b J d * y := by
  rw [g2k_P_eq, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
    hy, mul_one, one_mul]

theorem g2k_commute_one_sub_P {y : Matrix (Fin n) (Fin n) ℂ}
    (hy : y * g2k_Jm b J = g2k_Jm b J * y) :
    y * (1 - g2k_P b J d) = (1 - g2k_P b J d) * y := by
  rw [mul_sub, sub_mul, g2k_commute_P b J hy, mul_one, one_mul]

/-- The trace of an idempotent complex matrix is a natural number. -/
theorem g2k_exists_trace_eq_nat (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : Q * Q = Q) :
    ∃ r : ℕ, Q.trace = r := by
  have hqq : Matrix.toLin' Q * Matrix.toLin' Q = Matrix.toLin' Q := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hQ]
  have hproj := (LinearMap.isProj_range_iff_isIdempotentElem _).mpr hqq
  refine ⟨Module.finrank ℂ (LinearMap.range (Matrix.toLin' Q)), ?_⟩
  rw [← hproj.trace, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

/-- **The eigenspaces of `J` have equal dimension**: `tr P = n/2` and `n` is even. -/
theorem g2k_trace_P (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V)) :
    (g2k_P b J d).trace = ((n / 2 : ℕ) : ℂ) ∧ n = 2 * (n / 2) := by
  obtain ⟨r, hr0⟩ := g2k_exists_trace_eq_nat _ (g2k_P_mul_self b J hd hJ)
  have hr := hr0
  set t : ℚ := (LinearMap.toMatrix b b J).trace
  have htr : (g2k_Jm b J).trace = (t : ℂ) := by
    rw [g2k_Jm]
    exact (AddMonoidHom.map_trace (algebraMap ℚ ℂ).toAddMonoidHom _).symm
  have hP : (g2k_P b J d).trace = (1 / 2 : ℂ) * (n - g2k_c d * t) := by
    rw [g2k_P, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, htr, Matrix.trace_one]
    simp [smul_eq_mul]
  have hs : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hc : g2k_c d = Complex.I * (((Real.sqrt d)⁻¹ : ℝ) : ℂ) := by
    rw [g2k_c, div_eq_mul_inv, Complex.ofReal_inv]
  rw [hP, hc] at hr
  have him := congrArg Complex.im hr
  have hre := congrArg Complex.re hr
  simp at him hre
  have h2 : (n : ℝ) = 2 * r := by linear_combination 2 * hre
  have h3 : n = 2 * r := by exact_mod_cast h2
  refine ⟨?_, by omega⟩
  rw [hr0, show n / 2 = r by omega]

/-- `det (y + s + t J)` in `ℂ[s][t]`. -/
def g2k_Hy (y : Matrix (Fin n) (Fin n) ℂ) : ℂ[X][X] :=
  Matrix.det (y.map (fun z => C (C z)) + (C X : ℂ[X][X]) • (1 : Matrix (Fin n) (Fin n) ℂ[X][X]) +
    (X : ℂ[X][X]) • (g2k_Jm b J).map (fun z => C (C z)))

/-- The matrix of a coordinate vector. -/
def g2k_mat (x : Fin n × Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => x (i, j)

theorem g2k_aeval_coeff_kCharPoly (x : Fin n × Fin n → ℂ) (a c : ℕ) :
    MvPolynomial.aeval x (((g2_kCharPoly b J).coeff a).coeff c) =
      ((g2k_Hy b J (g2k_mat x)).coeff a).coeff c := by
  let ψ : MvPolynomial (Fin n × Fin n) ℚ →+* ℂ := (MvPolynomial.aeval x).toRingHom
  have h : (g2_kCharPoly b J).map (mapRingHom ψ) = g2k_Hy b J (g2k_mat x) := by
    rw [g2_kCharPoly, g2k_Hy, ← coe_mapRingHom, RingHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j <;> simp [g1_varMatrix, g2k_Jm, g2k_mat, Matrix.one_apply, ψ, hij]
  rw [← h, coeff_map, coe_mapRingHom, coeff_map]
  rfl

theorem g2k_subst_Hy (p q : ℂ) (y : Matrix (Fin n) (Fin n) ℂ) :
    g2k_subst p q (g2k_Hy b J y) =
      Matrix.det (y.map C + (X : ℂ[X]) • (p • 1 + q • g2k_Jm b J).map C) := by
  rw [g2k_Hy, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j <;> simp [g2k_subst, Matrix.one_apply, hij] <;> ring

/-- **The trace of the `k`-determinant.** For `y` commuting with `J`, `g2_kDetTrace` evaluates to
`det (y P + 1 - P) + det (y (1 - P) + P)`, the sum of the determinants of `y` on the two
eigenspaces of `J`. -/
theorem g2k_aeval_kDetTrace (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V))
    (x : Fin n × Fin n → ℂ) (hy : g2k_mat x * g2k_Jm b J = g2k_Jm b J * g2k_mat x) :
    MvPolynomial.aeval x (g2_kDetTrace b J d) =
      (g2k_mat x * g2k_P b J d + (1 - g2k_P b J d)).det +
        (g2k_mat x * (1 - g2k_P b J d) + g2k_P b J d).det := by
  obtain ⟨htrP, hn⟩ := g2k_trace_P b J hd hJ
  set m := n / 2 with hm
  set y := g2k_mat x
  set P := g2k_P b J d
  have htrQ : (1 - P).trace = (m : ℂ) := by
    rw [Matrix.trace_sub, Matrix.trace_one, htrP, Fintype.card_fin]
    conv_lhs => rw [hn]
    push_cast
    ring
  have hminus : (y * (1 - P) + P).det =
      (g2k_subst (1 / 2) (-g2k_c d / 2) (g2k_Hy b J y)).coeff m := by
    rw [g2k_subst_Hy, ← g2k_P_eq, g2k_coeff_det_add_X_smul y P (g2k_P_mul_self b J hd hJ)
      (g2k_commute_P b J hy) htrP]
  have hplus : (y * P + (1 - P)).det =
      (g2k_subst (1 / 2) (g2k_c d / 2) (g2k_Hy b J y)).coeff m := by
    rw [g2k_subst_Hy, ← g2k_one_sub_P_eq, g2k_coeff_det_add_X_smul y (1 - P)
      (g2k_one_sub_P_mul_self b J hd hJ) (g2k_commute_one_sub_P b J hy) htrQ, sub_sub_cancel]
  rw [hplus, hminus, g2k_coeff_subst, g2k_coeff_subst, ← Finset.sum_add_distrib]
  set cb : ℕ → ℂ := fun k => ((g2k_Hy b J y).coeff k).coeff (m - k) with hcb
  have h1 : ∀ k ∈ Finset.range (m + 1),
      (g2k_c d / 2) ^ k * (1 / 2) ^ (m - k) * ((g2k_Hy b J y).coeff k).coeff (m - k) +
        (-g2k_c d / 2) ^ k * (1 / 2) ^ (m - k) * ((g2k_Hy b J y).coeff k).coeff (m - k) =
      (1 + (-1) ^ k) * ((g2k_c d / 2) ^ k * (1 / 2) ^ (m - k) * cb k) := by
    intro k _
    rw [neg_div, neg_pow]
    ring
  rw [Finset.sum_congr rfl h1, g2k_sum_even, g2_kDetTrace, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : 2 * j ≤ m := by
    have := Finset.mem_range.mp hj
    omega
  rw [map_mul, MvPolynomial.aeval_C, g2k_aeval_coeff_kCharPoly]
  obtain ⟨k, hk⟩ : ∃ k, m = 2 * j + k := ⟨m - 2 * j, by omega⟩
  simp only [cb, ← hm, y]
  rw [hk, Nat.add_sub_cancel_left]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have key : (algebraMap ℚ ℂ) (2 / 2 ^ (2 * j + k) / (-d) ^ j) =
      2 * ((g2k_c d / 2) ^ (2 * j) * (1 / 2) ^ k) := by
    rw [pow_mul, div_pow, g2k_c_sq hd, eq_ratCast]
    push_cast
    have e : (-1 / (d : ℂ) / 2 ^ 2) = ((-(d : ℂ)) * 2 ^ 2)⁻¹ := by
      field_simp
    rw [e, inv_pow, mul_pow, one_div_pow, pow_add, pow_mul]
    field_simp
  rw [key]
  ring

end Proj

/-! ## Membership in `G_k` -/

section Mem

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ}

theorem g2k_mat_coords (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    g2k_mat (g1_coords g) = (g : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  rfl

theorem g2k_mapMatrix_varMatrix (x : Fin n × Fin n → ℂ) :
    (MvPolynomial.aeval (R := ℚ) x).mapMatrix (g1_varMatrix ℚ n) = g2k_mat x := by
  ext i j
  simp [g1_varMatrix, g2k_mat]

theorem g2k_mapMatrix_map_C (x : Fin n × Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℚ) :
    (MvPolynomial.aeval (R := ℚ) x).mapMatrix (M.map MvPolynomial.C) = M.map (algebraMap ℚ ℂ) := by
  ext i j
  simp

theorem g2k_aeval_commEquations (x : Fin n × Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) :
    MvPolynomial.aeval x (g2_commEquations M i j) =
      (g2k_mat x * M.map (algebraMap ℚ ℂ) - M.map (algebraMap ℚ ℂ) * g2k_mat x) i j := by
  rw [← g2k_mapMatrix_varMatrix, ← g2k_mapMatrix_map_C, ← map_mul, ← map_mul, ← map_sub]
  rfl

theorem g2k_aeval_isometryEquations (x : Fin n × Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) :
    MvPolynomial.aeval x (g1_isometryEquations M i j) =
      (Matrix.transpose (g2k_mat x) * M.map (algebraMap ℚ ℂ) * g2k_mat x -
        M.map (algebraMap ℚ ℂ)) i j := by
  have hT : (MvPolynomial.aeval (R := ℚ) x).mapMatrix (Matrix.transpose (g1_varMatrix ℚ n)) =
      Matrix.transpose (g2k_mat x) := by
    rw [← g2k_mapMatrix_varMatrix]
    rfl
  rw [← hT, ← g2k_mapMatrix_varMatrix, ← g2k_mapMatrix_map_C, ← map_mul, ← map_mul, ← map_sub]
  rfl

theorem g2k_aeval_det_sub_one (x : Fin n × Fin n → ℂ) :
    MvPolynomial.aeval x ((g1_varMatrix ℚ n).det - 1) = (g2k_mat x).det - 1 := by
  rw [map_sub, map_one, ← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 2
  exact g2k_mapMatrix_varMatrix x

theorem g2k_matrix_eq_iff_entries {A B : Matrix (Fin n) (Fin n) ℂ} :
    A = B ↔ ∀ i j, (A - B) i j = 0 := by
  rw [← sub_eq_zero, Matrix.ext_iff.symm]
  simp

variable (b : Module.Basis (Fin n) ℚ V) (E : LinearMap.BilinForm ℚ V)
  (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V) (d : ℚ)

/-- Membership in `G_k`, with the equations evaluated. -/
theorem g2k_mem_gkGroup_iff_eqs (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    g ∈ g2_gkGroup b E R J d ↔
      (∀ r ∈ R, (g : Matrix (Fin n) (Fin n) ℂ) * (LinearMap.toMatrix b b r).map (algebraMap ℚ ℂ) =
          (LinearMap.toMatrix b b r).map (algebraMap ℚ ℂ) * g) ∧
      (g : Matrix (Fin n) (Fin n) ℂ) * g2k_Jm b J = g2k_Jm b J * g ∧
      Matrix.transpose (g : Matrix (Fin n) (Fin n) ℂ) *
          (LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ) * g =
        (LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ) ∧
      (g : Matrix (Fin n) (Fin n) ℂ).det = 1 ∧
      MvPolynomial.aeval (g1_coords g) (g2_kDetTrace b J d) = 2 := by
  have hx := g2k_mat_coords g
  simp only [g2_gkGroup, g2_ratZeroSet, g2_gkEquations, Set.mem_ofPred_eq, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  simp only [g2k_matrix_eq_iff_entries, g2k_Jm]
  constructor
  · intro h
    refine ⟨fun r hr i j => ?_, fun i j => ?_, fun i j => ?_, ?_, ?_⟩
    · have := h _ (Or.inl (Or.inl (Or.inl ⟨r, hr, i, j, rfl⟩)))
      rwa [g2k_aeval_commEquations, hx] at this
    · have := h _ (Or.inl (Or.inl (Or.inr ⟨i, j, rfl⟩)))
      rwa [g2k_aeval_commEquations, hx] at this
    · have := h _ (Or.inl (Or.inr ⟨i, j, rfl⟩))
      rwa [g2k_aeval_isometryEquations, hx] at this
    · have := h _ (Or.inr (Or.inl rfl))
      rwa [g2k_aeval_det_sub_one, hx, sub_eq_zero] at this
    · have := h _ (Or.inr (Or.inr rfl))
      rwa [map_sub, map_ofNat, sub_eq_zero] at this
  · rintro ⟨h1, h2, h3, h4, h5⟩ f hf
    rcases hf with (((⟨r, hr, i, j, rfl⟩ | ⟨i, j, rfl⟩) | ⟨i, j, rfl⟩) | rfl | rfl)
    · rw [g2k_aeval_commEquations, hx]
      exact h1 r hr i j
    · rw [g2k_aeval_commEquations, hx]
      exact h2 i j
    · rw [g2k_aeval_isometryEquations, hx]
      exact h3 i j
    · rw [g2k_aeval_det_sub_one, hx, h4, sub_self]
    · rw [map_sub, map_ofNat, h5, sub_self]

theorem g2k_mul_add_iff (a c : ℂ) : a * c = 1 ∧ a + c = 2 ↔ a = 1 ∧ c = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : (a - 1) ^ 2 = 0 := by linear_combination a * h2 - h1
    have ha : a = 1 := by simpa [sub_eq_zero] using h3
    refine ⟨ha, ?_⟩
    rw [ha] at h2
    linear_combination h2
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- Membership in `G_k` with the determinants on the two eigenspaces. -/
theorem g2k_mem_gkGroup_iff {d : ℚ} (hd : 0 < d) (hJ : J * J = (-d) • (1 : Module.End ℚ V))
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    g ∈ g2_gkGroup b E R J d ↔
      (∀ r ∈ R, (g : Matrix (Fin n) (Fin n) ℂ) * (LinearMap.toMatrix b b r).map (algebraMap ℚ ℂ) =
          (LinearMap.toMatrix b b r).map (algebraMap ℚ ℂ) * g) ∧
      (g : Matrix (Fin n) (Fin n) ℂ) * g2k_Jm b J = g2k_Jm b J * g ∧
      Matrix.transpose (g : Matrix (Fin n) (Fin n) ℂ) *
          (LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ) * g =
        (LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ) ∧
      ((g : Matrix (Fin n) (Fin n) ℂ) * g2k_P b J d + (1 - g2k_P b J d)).det = 1 ∧
      ((g : Matrix (Fin n) (Fin n) ℂ) * (1 - g2k_P b J d) + g2k_P b J d).det = 1 := by
  rw [g2k_mem_gkGroup_iff_eqs]
  refine and_congr_right' (and_congr_right fun hB => and_congr_right' ?_)
  have hk := g2k_aeval_kDetTrace b J hd hJ (g1_coords g) (by rw [g2k_mat_coords]; exact hB)
  rw [g2k_mat_coords] at hk
  have hdet : (g : Matrix (Fin n) (Fin n) ℂ).det =
      ((g : Matrix (Fin n) (Fin n) ℂ) * g2k_P b J d + (1 - g2k_P b J d)).det *
        ((g : Matrix (Fin n) (Fin n) ℂ) * (1 - g2k_P b J d) + g2k_P b J d).det := by
    rw [← Matrix.det_mul, g2k_proj_mul_compl _ _ (g2k_P_mul_self b J hd hJ)
      (g2k_commute_P b J hB)]
  rw [hk, hdet]
  exact g2k_mul_add_iff _ _

theorem g2k_comm_inv (x : Matrix.GeneralLinearGroup (Fin n) ℂ) (M : Matrix (Fin n) (Fin n) ℂ)
    (h : (x : Matrix (Fin n) (Fin n) ℂ) * M = M * x) :
    ((x⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * M =
      M * ((x⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
  set y := ((x⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have h1 : (x : Matrix (Fin n) (Fin n) ℂ) * y = 1 := Units.mul_inv x
  have h2 : y * (x : Matrix (Fin n) (Fin n) ℂ) = 1 := Units.inv_mul x
  calc y * M = y * M * ((x : Matrix (Fin n) (Fin n) ℂ) * y) := by rw [h1, mul_one]
    _ = y * ((x : Matrix (Fin n) (Fin n) ℂ) * M) * y := by rw [h]; simp only [mul_assoc]
    _ = M * y := by rw [← mul_assoc, h2, one_mul]

theorem g2k_comm_mul (x y M : Matrix (Fin n) (Fin n) ℂ) (hx : x * M = M * x) (hy : y * M = M * y) :
    x * y * M = M * (x * y) := by
  rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]

/-- **`G_k` is a `ℚ`-algebraic subgroup.** -/
theorem g2k_isRatAlgSubgroup_gkGroup {d : ℚ} (hd : 0 < d)
    (hJ : J * J = (-d) • (1 : Module.End ℚ V)) :
    g2_IsRatAlgSubgroup (g2_gkGroup b E R J d) := by
  set P := g2k_P b J d
  have hP := g2k_P_mul_self b J hd hJ
  have hQ := g2k_one_sub_P_mul_self b J hd hJ
  set Ω := (LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ)
  refine ⟨⟨_, rfl⟩, ?_, ?_, ?_⟩
  · rw [g2k_mem_gkGroup_iff b E R J hd hJ]
    simp [P]
  · intro x hx y hy
    rw [g2k_mem_gkGroup_iff b E R J hd hJ] at hx hy ⊢
    obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx
    obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := hy
    rw [Units.val_mul]
    refine ⟨fun r hr => g2k_comm_mul _ _ _ (hx1 r hr) (hy1 r hr), g2k_comm_mul _ _ _ hx2 hy2,
      (g1_isometrySubgroup Ω).mul_mem hx3 hy3, ?_, ?_⟩
    · rw [← g2k_proj_mul_proj _ _ _ hP (g2k_commute_P b J hy2), Matrix.det_mul, hx4, hy4, mul_one]
    · have h := g2k_proj_mul_proj (x : Matrix (Fin n) (Fin n) ℂ) (1 - P) y hQ
        (g2k_commute_one_sub_P b J hy2)
      rw [sub_sub_cancel] at h
      rw [← h, Matrix.det_mul, hx5, hy5, mul_one]
  · intro x hx
    rw [g2k_mem_gkGroup_iff b E R J hd hJ] at hx ⊢
    obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx
    have hi2 := g2k_comm_inv x _ hx2
    have hinv : ((x⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *
        (x : Matrix (Fin n) (Fin n) ℂ) = 1 := Units.inv_mul x
    refine ⟨fun r hr => g2k_comm_inv x _ (hx1 r hr), hi2,
      (g1_isometrySubgroup Ω).inv_mem hx3, ?_, ?_⟩
    · have h := g2k_proj_mul_proj
        ((x⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) P _ hP
        (g2k_commute_P b J hx2)
      rw [hinv, one_mul, add_sub_cancel] at h
      have h' := congrArg Matrix.det h
      rw [Matrix.det_mul, hx4, mul_one, Matrix.det_one] at h'
      exact h'
    · have h := g2k_proj_mul_proj
        ((x⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (1 - P) _ hQ
        (g2k_commute_one_sub_P b J hx2)
      rw [hinv, one_mul, sub_sub_cancel, sub_add_cancel] at h
      have h' := congrArg Matrix.det h
      rw [Matrix.det_mul, hx5, mul_one, Matrix.det_one] at h'
      exact h'

end Mem

end HodgeLean.Foundations
