import HodgeLean.Foundations.MatrixAlgGroupLie

/-! # Tori of frames (Track G2, helpers for the Lie bridge)

A frame is a family of orthogonal idempotent matrices `Q i` summing to `1`, with integer weights
`w i`; its torus is `t ↦ Σ t^{w i} Q i` and its grading matrix `D_Q = Σ w i Q i`.

* `g2l_differential_frameD_eq_zero`, `g2l_frameD_mem_lieOfSet`: `D_Q` is tangent to the torus
  (one-variable Laurent polynomials: a Laurent polynomial vanishing on `ℂˣ` has zero
  logarithmic derivative at `1`).
* `g2l_torus_vanish_of_infinite`: a polynomial vanishing at infinitely many torus points
  vanishes on the torus.
* `g2l_isIrreducible_torus`, `g2l_isIrreducible_mul`: tori and products of irreducible sets are
  Zariski irreducible.
* `g2l_weightComp_mem`: a subspace stable under `ad D_Q` contains the weight components of its
  elements (Lagrange interpolation).

Sources: Borel, *Linear Algebraic Groups*, 2nd ed., §2.2, §8.2–8.6; Humphreys, *Linear Algebraic
Groups*, §16.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace HodgeLean.Foundations

open MvPolynomial
open scoped Pointwise

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

section Frame

variable {A : Type*} [CommRing A]

/-- A frame: a finite family of pairwise orthogonal idempotent matrices summing to `1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.4 (diagonalizable endomorphisms, the decomposition into eigenspaces); Bourbaki, *Algèbre*, ch. VIII (orthogonal idempotents). -/
def g2l_IsFrame (Q : ι → Matrix (Fin n) (Fin n) A) : Prop :=
  (∀ i, Q i * Q i = Q i) ∧ (∀ i j, i ≠ j → Q i * Q j = 0) ∧ ∑ i, Q i = 1

example : @g2l_IsFrame = @g2l_IsFrame := rfl

theorem g2l_IsFrame.map {B : Type*} [CommRing B] {Q : ι → Matrix (Fin n) (Fin n) A}
    (hQ : g2l_IsFrame Q) (φ : A →+* B) : g2l_IsFrame (fun i => (Q i).map φ) := by
  refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
  · rw [← Matrix.map_mul, hQ.1 i]
  · rw [← Matrix.map_mul, hQ.2.1 i j hij, Matrix.map_zero _ (map_zero φ)]
  · have h := map_sum φ.mapMatrix Q Finset.univ
    simp only [RingHom.mapMatrix_apply] at h
    rw [← h, hQ.2.2, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem g2l_IsFrame.mul_eq {Q : ι → Matrix (Fin n) (Fin n) A} (hQ : g2l_IsFrame Q) (i j : ι) :
    Q i * Q j = if i = j then Q i else 0 := by
  split_ifs with h
  · subst h; exact hQ.1 i
  · exact hQ.2.1 i j h

/-- The torus matrix `Σ τ^{w i} Q i` attached to a unit `τ`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.5–8.6 (one-parameter subgroups of a torus, cocharacters). -/
def g2l_torusAt (Q : ι → Matrix (Fin n) (Fin n) A) (w : ι → ℤ) (τ : Aˣ) :
    Matrix (Fin n) (Fin n) A :=
  ∑ i, ((τ ^ w i : Aˣ) : A) • Q i

example : @g2l_torusAt = @g2l_torusAt := rfl

/-- The grading matrix `Σ w i Q i` of a frame.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.6 (the differential of a cocharacter); Deligne, *Théorie de Hodge II*, §2.1. -/
def g2l_frameD (Q : ι → Matrix (Fin n) (Fin n) A) (w : ι → ℤ) : Matrix (Fin n) (Fin n) A :=
  ∑ i, (w i : A) • Q i

example : @g2l_frameD = @g2l_frameD := rfl

variable {Q : ι → Matrix (Fin n) (Fin n) A} (w : ι → ℤ)

theorem g2l_proj_mul_sum (hQ : g2l_IsFrame Q) (c : ι → A) (i : ι) :
    Q i * ∑ j, c j • Q j = c i • Q i := by
  rw [Finset.mul_sum]
  simp_rw [Matrix.mul_smul, hQ.mul_eq]
  simp

theorem g2l_sum_mul_proj (hQ : g2l_IsFrame Q) (c : ι → A) (i : ι) :
    (∑ j, c j • Q j) * Q i = c i • Q i := by
  rw [Finset.sum_mul]
  simp_rw [Matrix.smul_mul, hQ.mul_eq]
  simp [eq_comm]

theorem g2l_sum_mul_sum (hQ : g2l_IsFrame Q) (c d : ι → A) :
    (∑ j, c j • Q j) * (∑ j, d j • Q j) = ∑ j, (c j * d j) • Q j := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mul, g2l_proj_mul_sum hQ, smul_smul]

theorem g2l_torusAt_mul (hQ : g2l_IsFrame Q) (τ τ' : Aˣ) :
    g2l_torusAt Q w τ * g2l_torusAt Q w τ' = g2l_torusAt Q w (τ * τ') := by
  rw [g2l_torusAt, g2l_torusAt, g2l_sum_mul_sum hQ, g2l_torusAt]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_zpow, Units.val_mul]

omit [DecidableEq ι] in
theorem g2l_torusAt_one (hQ : g2l_IsFrame Q) : g2l_torusAt Q w 1 = 1 := by
  simp [g2l_torusAt, hQ.2.2]

theorem g2l_torusAt_map {B : Type*} [CommRing B] (φ : A →+* B) (τ : Aˣ) :
    (g2l_torusAt Q w τ).map φ = g2l_torusAt (fun i => (Q i).map φ) w (Units.map φ τ) := by
  have h := map_sum φ.mapMatrix (fun i => ((τ ^ w i : Aˣ) : A) • Q i) Finset.univ
  simp only [RingHom.mapMatrix_apply] at h
  rw [g2l_torusAt, g2l_torusAt, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.map_smul' _ _ _ (map_mul φ), ← map_zpow]
  rfl

theorem g2l_frameD_map {B : Type*} [CommRing B] (φ : A →+* B) :
    (g2l_frameD Q w).map φ = g2l_frameD (fun i => (Q i).map φ) w := by
  have h := map_sum φ.mapMatrix (fun i => (w i : A) • Q i) Finset.univ
  simp only [RingHom.mapMatrix_apply] at h
  rw [g2l_frameD, g2l_frameD, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.map_smul' _ _ _ (map_mul φ), map_intCast]

/-- `Y = Σ_{i,j} Q i Y Q j`. -/
theorem g2l_eq_sum_blocks (hQ : g2l_IsFrame Q) (Y : Matrix (Fin n) (Fin n) A) :
    Y = ∑ p : ι × ι, Q p.1 * Y * Q p.2 := by
  calc Y = (∑ i, Q i) * Y * (∑ j, Q j) := by rw [hQ.2.2, one_mul, mul_one]
    _ = ∑ i, ∑ j, Q i * Y * Q j := by
        rw [Finset.sum_mul, Finset.sum_mul_sum]
    _ = ∑ p : ι × ι, Q p.1 * Y * Q p.2 := (Fintype.sum_prod_type' _).symm

/-- Conjugation of a matrix by a torus matrix, block by block. -/
theorem g2l_torusAt_conj (hQ : g2l_IsFrame Q) (τ : Aˣ) (Y : Matrix (Fin n) (Fin n) A) :
    g2l_torusAt Q w τ⁻¹ * Y * g2l_torusAt Q w τ =
      ∑ p : ι × ι, ((τ ^ (w p.2 - w p.1) : Aˣ) : A) • (Q p.1 * Y * Q p.2) := by
  conv_lhs => rw [g2l_eq_sum_blocks hQ Y]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [g2l_torusAt, g2l_torusAt, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    g2l_sum_mul_proj hQ, Matrix.mul_assoc, Matrix.mul_assoc, g2l_proj_mul_sum hQ,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, ← Units.val_mul,
    inv_zpow', ← zpow_add, Matrix.mul_assoc]
  congr 3
  ring

/-- The bracket with the grading matrix acts on the block `(i, j)` by `w i - w j`. -/
theorem g2l_frameD_bracket_block (hQ : g2l_IsFrame Q) (Y : Matrix (Fin n) (Fin n) A) (i j : ι) :
    g2l_frameD Q w * (Q i * Y * Q j) - (Q i * Y * Q j) * g2l_frameD Q w =
      ((w i : A) - w j) • (Q i * Y * Q j) := by
  rw [g2l_frameD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, g2l_sum_mul_proj hQ, Matrix.mul_assoc,
    Matrix.mul_assoc, g2l_proj_mul_sum hQ, sub_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

end Frame

section Mono

variable {A : Type*} [CommRing A]

/-- The Laurent monomial `T^k` (`k ≥ 0`) or `U^{-k}` (`k < 0`).
Source: Bourbaki, *Algèbre*, ch. IV (Laurent polynomials). -/
def g2l_mono (T U : A) (k : ℤ) : A :=
  if 0 ≤ k then T ^ k.toNat else U ^ (-k).toNat

example : @g2l_mono = @g2l_mono := rfl

theorem g2l_mono_units (τ : Aˣ) (k : ℤ) : g2l_mono (τ : A) (τ⁻¹ : Aˣ) k = ((τ ^ k : Aˣ) : A) := by
  unfold g2l_mono
  split_ifs with hk
  · rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, Int.toNat_of_nonneg hk]
  · rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, Int.toNat_of_nonneg (by omega), inv_zpow',
      neg_neg]

theorem g2l_mono_map {B : Type*} [CommRing B] (φ : A →+* B) (T U : A) (k : ℤ) :
    φ (g2l_mono T U k) = g2l_mono (φ T) (φ U) k := by
  unfold g2l_mono
  split_ifs <;> simp

/-- A derivation with `D T = c T`, `D U = - c U` acts on `g2l_mono T U k` by `c k`. -/
theorem g2l_derivation_mono {R : Type*} [CommRing R] [Algebra R A] (D : Derivation R A A)
    (T U c : A) (hT : D T = c * T) (hU : D U = -(c * U)) (k : ℤ) :
    D (g2l_mono T U k) = (c * k) * g2l_mono T U k := by
  unfold g2l_mono
  split_ifs with hk
  · rw [Derivation.leibniz_pow, hT]
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simp only [Int.toNat_natCast, nsmul_eq_mul, smul_eq_mul, Int.cast_natCast]
    cases m with
    | zero => simp
    | succ m => simp only [Nat.add_sub_cancel, pow_succ]; ring
  · rw [Derivation.leibniz_pow, hU]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, -k = m := ⟨(-k).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hk' : (k : A) = -(m : A) := by
      have : k = -(m : ℤ) := by omega
      rw [this]; push_cast; ring
    rw [hm, hk']
    simp only [Int.toNat_natCast, nsmul_eq_mul, smul_eq_mul]
    cases m with
    | zero => simp
    | succ m => simp only [Nat.add_sub_cancel, pow_succ]; ring

/-- The two-variable torus matrix `Σ mono(w i) Q i`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.5 (the coordinate ring of `G_m` is `k[T, T⁻¹]`). -/
def g2l_psi (Q : ι → Matrix (Fin n) (Fin n) A) (w : ι → ℤ) (T U : A) :
    Matrix (Fin n) (Fin n) A :=
  ∑ i, g2l_mono T U (w i) • Q i

example : @g2l_psi = @g2l_psi := rfl

theorem g2l_psi_units (Q : ι → Matrix (Fin n) (Fin n) A) (w : ι → ℤ) (τ : Aˣ) :
    g2l_psi Q w (τ : A) (τ⁻¹ : Aˣ) = g2l_torusAt Q w τ := by
  simp only [g2l_psi, g2l_mono_units, g2l_torusAt]

theorem g2l_psi_map {B : Type*} [CommRing B] (Q : ι → Matrix (Fin n) (Fin n) A) (w : ι → ℤ)
    (φ : A →+* B) (T U : A) :
    (g2l_psi Q w T U).map φ = g2l_psi (fun i => (Q i).map φ) w (φ T) (φ U) := by
  have h := map_sum φ.mapMatrix (fun i => g2l_mono T U (w i) • Q i) Finset.univ
  simp only [RingHom.mapMatrix_apply] at h
  rw [g2l_psi, g2l_psi, h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.map_smul' _ _ _ (map_mul φ), g2l_mono_map]

/-- A derivation with `D T = c T`, `D U = - c U`, killing the entries of a frame, sends `ψ` to
`c ψ D_Q`. -/
theorem g2l_derivation_psi {R : Type*} [CommRing R] [Algebra R A] (D : Derivation R A A)
    {Q : ι → Matrix (Fin n) (Fin n) A} (hQ : g2l_IsFrame Q) (hD : ∀ i a b, D (Q i a b) = 0)
    (w : ι → ℤ) (T U c : A) (hT : D T = c * T) (hU : D U = -(c * U)) :
    (g2l_psi Q w T U).map D = c • (g2l_psi Q w T U * g2l_frameD Q w) := by
  rw [g2l_psi, g2l_frameD, g2l_sum_mul_sum hQ, Finset.smul_sum]
  ext a b
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
    Derivation.leibniz, hD, g2l_derivation_mono D T U c hT hU]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Mono

section Laurent

/-- `t^D F(t, 1/t)` as a polynomial in `t`, `D` the largest `Y`-degree of `F`.
Source: Bourbaki, *Algèbre*, ch. IV, §1 (clearing denominators of a Laurent polynomial). -/
def g2l_clear (F : MvPolynomial (Fin 2) ℂ) : Polynomial ℂ :=
  ∑ m ∈ F.support, Polynomial.monomial (m 0 + F.support.sup (fun m => m 1) - m 1) (F.coeff m)

example : @g2l_clear = @g2l_clear := rfl

theorem g2l_eval_clear (F : MvPolynomial (Fin 2) ℂ) {t : ℂ} (ht : t ≠ 0) :
    (g2l_clear F).eval t = t ^ (F.support.sup fun m => m 1) * eval ![t, t⁻¹] F := by
  rw [g2l_clear, Polynomial.eval_finsetSum, eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle : m 1 ≤ F.support.sup (fun m => m 1) := Finset.le_sup (f := fun m => m 1) hm
  rw [Polynomial.eval_monomial, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, inv_pow]
  set D := F.support.sup (fun m => m 1)
  rw [show m 0 + D - m 1 = m 0 + (D - m 1) by omega, pow_add]
  conv_rhs => rw [show D = (D - m 1) + m 1 by omega, pow_add]
  have : t ^ m 1 ≠ 0 := pow_ne_zero _ ht
  field_simp

theorem g2l_laurent_dichotomy (F : MvPolynomial (Fin 2) ℂ) :
    (∀ t : ℂ, t ≠ 0 → eval ![t, t⁻¹] F = 0) ∨
      {t : ℂ | t ≠ 0 ∧ eval ![t, t⁻¹] F = 0}.Finite := by
  by_cases hG : g2l_clear F = 0
  · left
    intro t ht
    have := g2l_eval_clear F ht
    rw [hG, Polynomial.eval_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ ht)
  · right
    refine (Polynomial.finite_setOfPred_isRoot hG).subset fun t ⟨ht, h⟩ => ?_
    change Polynomial.IsRoot _ t
    rw [Polynomial.IsRoot, g2l_eval_clear F ht, h, mul_zero]

theorem g2l_infinite_ne_zero : {t : ℂ | t ≠ 0}.Infinite := by
  have := (Set.infinite_univ (α := ℂ)).sdiff (Set.finite_singleton 0)
  convert this using 1
  ext t
  simp

theorem g2l_clear_eq_zero (F : MvPolynomial (Fin 2) ℂ)
    (h : ∀ t : ℂ, t ≠ 0 → eval ![t, t⁻¹] F = 0) : g2l_clear F = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine g2l_infinite_ne_zero.mono fun t ht => ?_
  change Polynomial.IsRoot _ t
  rw [Polynomial.IsRoot, g2l_eval_clear F ht, h t ht, mul_zero]

/-- The Euler derivation `X ∂_X - Y ∂_Y` of `ℂ[X, Y]`.
Source: Kaplansky, *An Introduction to Differential Algebra*, §1 (derivations of polynomial rings). -/
def g2l_euler : Derivation ℂ (MvPolynomial (Fin 2) ℂ) (MvPolynomial (Fin 2) ℂ) :=
  mkDerivation ℂ ![X 0, -X 1]

example : @g2l_euler = @g2l_euler := rfl

theorem g2l_euler_X0 : g2l_euler (X 0) = 1 * X 0 := by simp [g2l_euler]

theorem g2l_euler_X1 : g2l_euler (X 1) = -(1 * X 1) := by simp [g2l_euler]

theorem g2l_eval_euler (F : MvPolynomial (Fin 2) ℂ) :
    eval ![1, 1] (g2l_euler F) = ∑ m ∈ F.support, F.coeff m * ((m 0 : ℂ) - m 1) := by
  have h11 : (![1, 1] : Fin 2 → ℂ) = fun _ => 1 := by
    funext i; fin_cases i <;> rfl
  conv_lhs => rw [F.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [g2l_euler, mkDerivation_monomial, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  simp only [smul_eq_mul, map_mul, map_add, eval_monomial, Matrix.cons_val_zero,
    Matrix.cons_val_one, map_neg, eval_X, Finsupp.prod, Algebra.smul_def, algebraMap_eq, eval_C]
  rw [h11]
  simp only [one_pow, Finset.prod_const_one, mul_one]
  ring

theorem g2l_euler_sum_eq_zero (F : MvPolynomial (Fin 2) ℂ)
    (h : ∀ t : ℂ, t ≠ 0 → eval ![t, t⁻¹] F = 0) :
    ∑ m ∈ F.support, F.coeff m * ((m 0 : ℂ) - m 1) = 0 := by
  have hG := g2l_clear_eq_zero F h
  set D := F.support.sup (fun m => m 1)
  have h1 : (Polynomial.derivative (g2l_clear F)).eval 1 =
      ∑ m ∈ F.support, F.coeff m * ((m 0 : ℂ) + D - m 1) := by
    rw [g2l_clear, map_sum, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hle : m 1 ≤ D := Finset.le_sup (f := fun m => m 1) hm
    rw [Polynomial.derivative_monomial, Polynomial.eval_monomial, one_pow, mul_one,
      Nat.cast_sub (by omega), Nat.cast_add]
  have h2 : (g2l_clear F).eval 1 = ∑ m ∈ F.support, F.coeff m := by
    rw [g2l_clear, Polynomial.eval_finsetSum]
    simp
  rw [hG, Polynomial.derivative_zero, Polynomial.eval_zero] at h1
  rw [hG, Polynomial.eval_zero] at h2
  have : ∑ m ∈ F.support, F.coeff m * ((m 0 : ℂ) - m 1) =
      ∑ m ∈ F.support, F.coeff m * ((m 0 : ℂ) + D - m 1) - D * ∑ m ∈ F.support, F.coeff m := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [this, ← h1, ← h2]
  ring

end Laurent

section Curve

variable {Q : ι → Matrix (Fin n) (Fin n) ℂ}

/-- The torus `t ↦ Σ t^{w i} Q i` of a complex frame, as a homomorphism `ℂˣ → GL_n(ℂ)`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.5 (cocharacters `G_m → GL_n`). -/
def g2l_torusGL (hQ : g2l_IsFrame Q) (w : ι → ℤ) : ℂˣ →* Matrix.GeneralLinearGroup (Fin n) ℂ where
  toFun t := ⟨g2l_torusAt Q w t, g2l_torusAt Q w t⁻¹,
    by rw [g2l_torusAt_mul w hQ, mul_inv_cancel, g2l_torusAt_one w hQ],
    by rw [g2l_torusAt_mul w hQ, inv_mul_cancel, g2l_torusAt_one w hQ]⟩
  map_one' := Units.ext (g2l_torusAt_one w hQ)
  map_mul' s t := Units.ext (g2l_torusAt_mul w hQ s t).symm

example : @g2l_torusGL = @g2l_torusGL := rfl

theorem g2l_torusGL_val (hQ : g2l_IsFrame Q) (w : ι → ℤ) (t : ℂˣ) :
    ((g2l_torusGL hQ w t : Matrix.GeneralLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      g2l_torusAt Q w t := rfl

/-- The entries of the two-variable torus matrix of a complex frame, at a point. -/
theorem g2l_eval_psi_entry (Q : ι → Matrix (Fin n) (Fin n) ℂ) (w : ι → ℤ) (x : Fin 2 → ℂ)
    (a b : Fin n) :
    eval x (g2l_psi (fun i => (Q i).map (C : ℂ →+* MvPolynomial (Fin 2) ℂ)) w (X 0) (X 1) a b) =
      g2l_psi Q w (x 0) (x 1) a b := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M a b)
    (g2l_psi_map (fun i => (Q i).map (C : ℂ →+* MvPolynomial (Fin 2) ℂ)) w
      (eval x) (X 0) (X 1))
  simp only [Matrix.map_apply, eval_X] at h
  rw [h]
  congr 2
  funext i
  ext c d
  simp

/-- Evaluating along the two-variable torus matrix. -/
theorem g2l_eval_aeval_psi (Q : ι → Matrix (Fin n) (Fin n) ℂ) (w : ι → ℤ) (x : Fin 2 → ℂ)
    (f : MvPolynomial (Fin n × Fin n) ℂ) :
    eval x (aeval (fun ab : Fin n × Fin n => g2l_psi (fun i => (Q i).map
      (C : ℂ →+* MvPolynomial (Fin 2) ℂ)) w (X 0) (X 1) ab.1 ab.2) f) =
      eval (fun ab : Fin n × Fin n => g2l_psi Q w (x 0) (x 1) ab.1 ab.2) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ab hp => simp only [map_mul, hp, aeval_X, eval_X, g2l_eval_psi_entry]

/-- **The grading matrix is tangent to its torus.** A polynomial vanishing on the torus of a
frame has zero differential at `1` along `D_Q = Σ w i Q i`. -/
theorem g2l_differential_frameD_eq_zero (hQ : g2l_IsFrame Q) (w : ι → ℤ)
    (f : MvPolynomial (Fin n × Fin n) ℂ)
    (hf : ∀ t : ℂˣ, eval (g1_coords (g2l_torusGL hQ w t)) f = 0) :
    g1_differential f (g2l_frameD Q w) = 0 := by
  set Qc : ι → Matrix (Fin n) (Fin n) (MvPolynomial (Fin 2) ℂ) :=
    fun i => (Q i).map (C : ℂ →+* MvPolynomial (Fin 2) ℂ)
  set Ψ := g2l_psi Qc w (X 0) (X 1)
  set F := aeval (fun ab : Fin n × Fin n => Ψ ab.1 ab.2) f
  have hpt : ∀ t : ℂ, t ≠ 0 → eval ![t, t⁻¹] F = 0 := by
    intro t ht
    rw [g2l_eval_aeval_psi]
    have := hf (Units.mk0 t ht)
    have hm : g2l_psi Q w t t⁻¹ = g2l_torusAt Q w (Units.mk0 t ht) := by
      simpa using g2l_psi_units Q w (Units.mk0 t ht)
    convert this using 2
    congr 1
    funext ab
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hm]
    rfl
  have hsum := g2l_euler_sum_eq_zero F hpt
  rw [← g2l_eval_euler] at hsum
  have hQc : g2l_IsFrame Qc := hQ.map C
  have hD : ∀ i a b, g2l_euler (Qc i a b) = 0 := fun i a b => by
    simp [Qc, Matrix.map_apply]
  have hder := g2l_derivation_psi g2l_euler hQc hD w (X 0) (X 1) 1 g2l_euler_X0 g2l_euler_X1
  rw [g1s_derivation_aeval, map_sum] at hsum
  have h1 : g2l_psi Q w (1 : ℂ) 1 = 1 := by
    have := g2l_psi_units Q w 1
    simp only [Units.val_one, inv_one] at this
    rw [this, g2l_torusAt_one w hQ]
  have h11 : (![1, 1] : Fin 2 → ℂ) 0 = 1 ∧ (![1, 1] : Fin 2 → ℂ) 1 = 1 := ⟨rfl, rfl⟩
  rw [g1_differential_apply, ← hsum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [map_mul, g2l_eval_aeval_psi, h11.1, h11.2, h1]
  congr 1
  have he := congrArg (fun M => M ab.1 ab.2) hder
  simp only [Matrix.map_apply] at he
  have hDentry : ∀ a b, eval ![1, 1] (g2l_frameD Qc w a b) = g2l_frameD Q w a b := by
    intro a b
    have hDm := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M a b) (g2l_frameD_map
      (Q := Qc) w (eval ![1, 1]))
    have hQe : (fun i => (Qc i).map (eval (![1, 1] : Fin 2 → ℂ))) = Q := by
      funext i; ext c d; simp [Qc]
    simp only [hQe, Matrix.map_apply] at hDm
    exact hDm
  rw [he, one_smul, Matrix.mul_apply, map_sum]
  simp only [map_mul, hDentry]
  simp only [Qc, g2l_eval_psi_entry, h11.1, h11.2, h1]
  simp [Matrix.one_apply]

/-- The polynomial `F(T, U)` of a polynomial `f` along the two-variable torus matrix, at `(t, 1/t)`,
is `f` at the torus point `t`. -/
theorem g2l_eval_aeval_psi_torus (hQ : g2l_IsFrame Q) (w : ι → ℤ)
    (f : MvPolynomial (Fin n × Fin n) ℂ) (t : ℂ) (ht : t ≠ 0) :
    eval ![t, t⁻¹] (aeval (fun ab : Fin n × Fin n => g2l_psi (fun i => (Q i).map
      (C : ℂ →+* MvPolynomial (Fin 2) ℂ)) w (X 0) (X 1) ab.1 ab.2) f) =
      eval (g1_coords (g2l_torusGL hQ w (Units.mk0 t ht))) f := by
  rw [g2l_eval_aeval_psi]
  have hm : g2l_psi Q w t t⁻¹ = g2l_torusAt Q w (Units.mk0 t ht) := by
    simpa using g2l_psi_units Q w (Units.mk0 t ht)
  congr 2
  funext ab
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hm]
  rfl

/-- A polynomial vanishes on the whole torus or at finitely many of its points. -/
theorem g2l_torus_dichotomy (hQ : g2l_IsFrame Q) (w : ι → ℤ)
    (f : MvPolynomial (Fin n × Fin n) ℂ) :
    (∀ t : ℂˣ, eval (g1_coords (g2l_torusGL hQ w t)) f = 0) ∨
      {t : ℂ | ∃ ht : t ≠ 0, eval (g1_coords (g2l_torusGL hQ w (Units.mk0 t ht))) f = 0}.Finite := by
  rcases g2l_laurent_dichotomy (aeval (fun ab : Fin n × Fin n => g2l_psi (fun i => (Q i).map
      (C : ℂ →+* MvPolynomial (Fin 2) ℂ)) w (X 0) (X 1) ab.1 ab.2) f) with h | h
  · left
    intro t
    have := h t t.ne_zero
    rw [g2l_eval_aeval_psi_torus hQ w f t t.ne_zero] at this
    convert this
    ext; simp
  · right
    refine h.subset fun t ⟨ht, h0⟩ => ⟨ht, ?_⟩
    rw [g2l_eval_aeval_psi_torus hQ w f t ht]
    exact h0

/-- A polynomial vanishing at infinitely many torus points vanishes on the torus. -/
theorem g2l_torus_vanish_of_infinite (hQ : g2l_IsFrame Q) (w : ι → ℤ)
    (f : MvPolynomial (Fin n × Fin n) ℂ) {E : Set ℂˣ} (hE : E.Infinite)
    (hf : ∀ t ∈ E, eval (g1_coords (g2l_torusGL hQ w t)) f = 0) (t : ℂˣ) :
    eval (g1_coords (g2l_torusGL hQ w t)) f = 0 := by
  rcases g2l_torus_dichotomy hQ w f with h | h
  · exact h t
  · exfalso
    refine hE (Set.Finite.of_finite_image (f := fun u : ℂˣ => (u : ℂ)) (h.subset ?_)
      (Units.val_injective.injOn))
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨u.ne_zero, ?_⟩
    convert hf u hu
    ext; simp

/-- The grading matrix of a frame lies in the tangent space of any set containing its torus. -/
theorem g2l_frameD_mem_lieOfSet (hQ : g2l_IsFrame Q) (w : ι → ℤ)
    {S : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)} (hS : ∀ t : ℂˣ, g2l_torusGL hQ w t ∈ S) :
    g2l_frameD Q w ∈ g1_lieOfSet S :=
  g1_mem_lieOfSet_iff.mpr fun f hf =>
    g2l_differential_frameD_eq_zero hQ w f fun t => g1_mem_vanishingIdealSet_iff.mp hf _ (hS t)

end Curve

section Irreducible

set_option warn.classDefReducibility false in
attribute [local instance] g1_zariski

/-- The torus of a frame is Zariski irreducible. -/
theorem g2l_isIrreducible_torus {Q : ι → Matrix (Fin n) (Fin n) ℂ} (hQ : g2l_IsFrame Q)
    (w : ι → ℤ) : IsIrreducible (Set.range (g2l_torusGL hQ w)) := by
  refine ⟨Set.range_nonempty _, isPreirreducible_iff_isClosed_union_isClosed.mpr ?_⟩
  intro Z₁ Z₂ h₁ h₂ hsub
  obtain ⟨s₁, rfl⟩ := (g1_isClosed_iff Z₁).mp h₁
  obtain ⟨s₂, rfl⟩ := (g1_isClosed_iff Z₂).mp h₂
  by_contra hcon
  push Not at hcon
  obtain ⟨hn₁, hn₂⟩ := hcon
  obtain ⟨_, ⟨t₁, rfl⟩, hg₁⟩ := Set.not_subset.mp hn₁
  obtain ⟨_, ⟨t₂, rfl⟩, hg₂⟩ := Set.not_subset.mp hn₂
  simp only [g1_zeroSet, Set.mem_ofPred_eq, not_forall] at hg₁ hg₂
  obtain ⟨f₁, hf₁, hv₁⟩ := hg₁
  obtain ⟨f₂, hf₂, hv₂⟩ := hg₂
  have hfin₁ := (g2l_torus_dichotomy hQ w f₁).resolve_left fun h => hv₁ (h t₁)
  have hfin₂ := (g2l_torus_dichotomy hQ w f₂).resolve_left fun h => hv₂ (h t₂)
  refine g2l_infinite_ne_zero ((hfin₁.union hfin₂).subset fun t ht => ?_)
  have ht' : t ≠ 0 := ht
  rcases hsub ⟨Units.mk0 t ht', rfl⟩ with h | h
  · exact Or.inl ⟨ht', h f₁ hf₁⟩
  · exact Or.inr ⟨ht', h f₂ hf₂⟩

/-- Right multiplication by `a` on matrix coordinates, as an algebra map: `x_ij ↦ Σ_l x_il a_lj`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.9 (right translations `ρ_a`). -/
def g2l_rightMulAlgHom {k : Type*} [Field k] (a : Matrix.GeneralLinearGroup (Fin n) k) :
    MvPolynomial (Fin n × Fin n) k →ₐ[k] MvPolynomial (Fin n × Fin n) k :=
  aeval fun ij => ∑ l, X (ij.1, l) * C ((a : Matrix (Fin n) (Fin n) k) l ij.2)

example : @g2l_rightMulAlgHom = @g2l_rightMulAlgHom := rfl

theorem g2l_eval_rightMulAlgHom {k : Type*} [Field k] (a g : Matrix.GeneralLinearGroup (Fin n) k)
    (f : MvPolynomial (Fin n × Fin n) k) :
    eval (g1_coords g) (g2l_rightMulAlgHom a f) = eval (g1_coords (g * a)) f := by
  have h : (eval (g1_coords g)).comp (g2l_rightMulAlgHom a).toRingHom =
      eval (g1_coords (g * a)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun ij => ?_)
    · simp
    · simp [g2l_rightMulAlgHom, g1_coords, Matrix.mul_apply]
  exact RingHom.congr_fun h f

/-- Right translations of `GL_n(k)` are continuous for the Zariski topology. -/
theorem g2l_continuous_mul_right {k : Type*} [Field k] (a : Matrix.GeneralLinearGroup (Fin n) k) :
    Continuous (fun g => g * a) := by
  have hφ : Continuous (fun g : Matrix.GeneralLinearGroup (Fin n) k =>
      (MvPolynomial.pointToPoint (k := k) (g1_coords g) :
        PrimeSpectrum (MvPolynomial (Fin n × Fin n) k))) := continuous_induced_dom
  refine continuous_induced_rng.mpr ?_
  have heq : (fun g : Matrix.GeneralLinearGroup (Fin n) k =>
      (MvPolynomial.pointToPoint (k := k) (g1_coords (g * a)) :
        PrimeSpectrum (MvPolynomial (Fin n × Fin n) k))) =
      PrimeSpectrum.comap (g2l_rightMulAlgHom a).toRingHom ∘
        (fun g => MvPolynomial.pointToPoint (k := k) (g1_coords g)) := by
    funext g
    ext f
    rw [Function.comp_apply, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
      g1_mem_pointToPoint_coords_iff, g1_mem_pointToPoint_coords_iff]
    change _ ↔ eval (g1_coords g) (g2l_rightMulAlgHom a f) = 0
    rw [g2l_eval_rightMulAlgHom]
  change Continuous (fun g : Matrix.GeneralLinearGroup (Fin n) k =>
      (MvPolynomial.pointToPoint (k := k) (g1_coords (g * a)) :
        PrimeSpectrum (MvPolynomial (Fin n × Fin n) k)))
  rw [heq]
  exact (PrimeSpectrum.continuous_comap _).comp hφ

/-- The product of two Zariski irreducible subsets of `GL_n(k)` is irreducible. -/
theorem g2l_isIrreducible_mul {k : Type*} [Field k]
    {A B : Set (Matrix.GeneralLinearGroup (Fin n) k)} (hA : IsIrreducible A)
    (hB : IsIrreducible B) : IsIrreducible (A * B) := by
  refine ⟨hA.nonempty.mul hB.nonempty, isPreirreducible_iff_isClosed_union_isClosed.mpr ?_⟩
  intro Z₁ Z₂ h₁ h₂ hsub
  have hrow : ∀ a ∈ A, (fun g => a * g) '' B ⊆ Z₁ ∨ (fun g => a * g) '' B ⊆ Z₂ := by
    intro a ha
    have hirr := hB.image _ (g1_continuous_mul_left a).continuousOn
    refine isPreirreducible_iff_isClosed_union_isClosed.mp hirr.2 Z₁ Z₂ h₁ h₂ ?_
    rintro _ ⟨b, hb, rfl⟩
    exact hsub (Set.mul_mem_mul ha hb)
  let C : Set (Matrix.GeneralLinearGroup (Fin n) k) → Set (Matrix.GeneralLinearGroup (Fin n) k) :=
    fun Z => ⋂ b ∈ B, (fun g => g * b) ⁻¹' Z
  have hC : ∀ Z, IsClosed Z → IsClosed (C Z) := fun Z hZ =>
    isClosed_biInter fun b _ => hZ.preimage (g2l_continuous_mul_right b)
  have hAC : A ⊆ C Z₁ ∪ C Z₂ := by
    intro a ha
    rcases hrow a ha with h | h
    · exact Or.inl (Set.mem_iInter₂.mpr fun b hb => h ⟨b, hb, rfl⟩)
    · exact Or.inr (Set.mem_iInter₂.mpr fun b hb => h ⟨b, hb, rfl⟩)
  rcases isPreirreducible_iff_isClosed_union_isClosed.mp hA.2 _ _ (hC Z₁ h₁) (hC Z₂ h₂) hAC with
    h | h
  · left
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Set.mem_iInter₂.mp (h ha) b hb
  · right
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Set.mem_iInter₂.mp (h ha) b hb

end Irreducible

section Lagrange

variable {Q : ι → Matrix (Fin n) (Fin n) ℂ}

/-- The `k`-th weight component `Σ_{w j - w i = k} Q i Y Q j` of a matrix.
Source: Humphreys, *Linear Algebraic Groups*, §16.4 (weight spaces of a torus acting by conjugation). -/
def g2l_weightComp (Q : ι → Matrix (Fin n) (Fin n) ℂ) (w : ι → ℤ) (k : ℤ)
    (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ p ∈ Finset.univ.filter (fun p : ι × ι => w p.2 - w p.1 = k), Q p.1 * Y * Q p.2

example : @g2l_weightComp = @g2l_weightComp := rfl

/-- The bracket with `D_Q`, as an endomorphism of `M_n(ℂ)`.
Source: Bourbaki, *Groupes et algèbres de Lie*, ch. I, §1 (the adjoint endomorphism). -/
def g2l_ad (D : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  LinearMap.mulLeft ℂ D - LinearMap.mulRight ℂ D

example : @g2l_ad = @g2l_ad := rfl

theorem g2l_ad_apply (D Y : Matrix (Fin n) (Fin n) ℂ) : g2l_ad D Y = D * Y - Y * D := rfl

theorem g2l_aeval_ad_block (hQ : g2l_IsFrame Q) (w : ι → ℤ) (P : Polynomial ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (i j : ι) :
    Polynomial.aeval (g2l_ad (g2l_frameD Q w)) P (Q i * Y * Q j) =
      P.eval ((w i : ℂ) - w j) • (Q i * Y * Q j) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, Polynomial.eval_add,
      add_smul]
  | monomial m a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply]
    have hpow : ∀ m : ℕ, (g2l_ad (g2l_frameD Q w) ^ m) (Q i * Y * Q j) =
        ((w i : ℂ) - w j) ^ m • (Q i * Y * Q j) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, g2l_ad_apply,
          g2l_frameD_bracket_block w hQ, smul_smul, pow_succ]
    rw [hpow, smul_smul, mul_comm]

/-- **Weight components stay in a bracket-stable subspace.** If a subspace `W` of `M_n(ℂ)` is
stable under the bracket with `D_Q`, it contains every weight component of its elements
(Lagrange interpolation in `ad D_Q`, which acts on the block `(i, j)` by `w i - w j`). -/
theorem g2l_weightComp_mem (hQ : g2l_IsFrame Q) (w : ι → ℤ)
    (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hW : ∀ Y ∈ W, g2l_frameD Q w * Y - Y * g2l_frameD Q w ∈ W) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : Y ∈ W) (k : ℤ) : g2l_weightComp Q w k Y ∈ W := by
  classical
  set K : Finset ℤ := Finset.univ.image (fun p : ι × ι => w p.2 - w p.1)
  set v : ℤ → ℂ := fun k => -(k : ℂ)
  have hv : Set.InjOn v K := fun a _ b _ h => by simpa [v] using h
  have hpoly : ∀ P : Polynomial ℂ, Polynomial.aeval (g2l_ad (g2l_frameD Q w)) P Y ∈ W := by
    intro P
    rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    clear! P
    induction m with
    | zero => simpa using hY
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hW _ ih
  by_cases hk : k ∈ K
  · have := hpoly (Lagrange.basis K v k)
    convert this using 1
    conv_rhs => rw [g2l_eq_sum_blocks hQ Y]
    rw [map_sum, g2l_weightComp, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [g2l_aeval_ad_block hQ w]
    have hp : (w p.1 : ℂ) - w p.2 = v (w p.2 - w p.1) := by simp [v]
    rw [hp]
    have hpK : w p.2 - w p.1 ∈ K := Finset.mem_image_of_mem _ (Finset.mem_univ p)
    split_ifs with h
    · rw [← h, Lagrange.eval_basis_self hv hpK, one_smul]
    · rw [Lagrange.eval_basis_of_ne (Ne.symm h) hpK, zero_smul]
  · have : g2l_weightComp Q w k Y = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      exact absurd ((Finset.mem_filter.mp hp).2 ▸ Finset.mem_image_of_mem _ (Finset.mem_univ p))
        hk
    rw [this]
    exact W.zero_mem

end Lagrange

end HodgeLean.Foundations
