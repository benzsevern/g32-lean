import HodgeLean.Foundations.Program.GaussManinToriVHS

/-!
# The Riemann bilinear relations for marked period data

For a Riemann form `A` of a period matrix `P`, the complex structure `J` on `ℝ^{2g}`, the
representation of every `ℂ`-linear form on `ℂ^g` as `E(t, ·) + i E(J t, ·)` on the lattice, and
the identity `Q(Aᵀ x, Aᵀ y) = E_ℂ(x, y)` for the dual form `Q = (A^{-1})ᵀ`. Together they give the
two Hodge--Riemann relations for `F¹ = H^{1,0}`. Helper names carry the prefix `d2v_`.
-/

noncomputable section

open scoped TensorProduct Matrix
namespace HodgeLean.Foundations.Program
open HodgeBlocks

variable {g : ℕ} {P : Fin g → Fin (2 * g) → ℂ}

/-- The complex structure of `ℂ^g` transported to `ℝ^{2g}` by the real map of a period matrix:
`P (J s) = i · P s`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §2.1 (the complex
structure `J` on `Λ ⊗ ℝ`). -/
def d2v_J (hP : d2_IsPeriodMatrix P) : (Fin (2 * g) → ℝ) →ₗ[ℝ] (Fin (2 * g) → ℝ) :=
  (LinearEquiv.ofBijective (d2_realMap P) (d2v_realMap_bijective hP)).symm.toLinearMap ∘ₗ
    ((Complex.I • LinearMap.id : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).restrictScalars ℝ) ∘ₗ
    d2_realMap P

example (hP : d2_IsPeriodMatrix P) : d2v_J hP 0 = 0 := map_zero _

theorem d2v_realMap_J (hP : d2_IsPeriodMatrix P) (s : Fin (2 * g) → ℝ) :
    d2_realMap P (d2v_J hP s) = Complex.I • d2_realMap P s := by
  have := (LinearEquiv.ofBijective (d2_realMap P) (d2v_realMap_bijective hP)).apply_symm_apply
    (Complex.I • d2_realMap P s)
  exact this

theorem d2v_J_J (hP : d2_IsPeriodMatrix P) (s : Fin (2 * g) → ℝ) :
    d2v_J hP (d2v_J hP s) = -s := by
  apply d2v_realMap_injective hP
  rw [d2v_realMap_J, d2v_realMap_J, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

theorem d2v_riemannReal_add_left (s s' t : Fin n → ℝ) :
    d2_riemannReal A (s + s') t = d2_riemannReal A s t + d2_riemannReal A s' t :=
  add_dotProduct _ _ _

theorem d2v_riemannReal_add_right (s t t' : Fin n → ℝ) :
    d2_riemannReal A s (t + t') = d2_riemannReal A s t + d2_riemannReal A s t' := by
  simp [d2_riemannReal, Matrix.mulVec_add, dotProduct_add]

theorem d2v_riemannReal_smul_left (c : ℝ) (s t : Fin n → ℝ) :
    d2_riemannReal A (c • s) t = c * d2_riemannReal A s t := by
  simp [d2_riemannReal, smul_dotProduct]

theorem d2v_riemannReal_smul_right (c : ℝ) (s t : Fin n → ℝ) :
    d2_riemannReal A s (c • t) = c * d2_riemannReal A s t := by
  simp [d2_riemannReal, Matrix.mulVec_smul, dotProduct_smul]

theorem d2v_riemannReal_neg_left (s t : Fin n → ℝ) :
    d2_riemannReal A (-s) t = -d2_riemannReal A s t := by
  simp [d2_riemannReal]

theorem d2v_riemannReal_neg_right (s t : Fin n → ℝ) :
    d2_riemannReal A s (-t) = -d2_riemannReal A s t := by
  simp [d2_riemannReal, Matrix.mulVec_neg]

theorem d2v_riemannReal_swap (hA : Aᵀ = -A) (s t : Fin n → ℝ) :
    d2_riemannReal A s t = -d2_riemannReal A t s := by
  have h : (A.map (Int.cast : ℤ → ℝ))ᵀ = -A.map (Int.cast : ℤ → ℝ) := by
    rw [← Matrix.transpose_map, hA]
    ext i j; simp
  unfold d2_riemannReal
  rw [Matrix.dotProduct_mulVec t, ← Matrix.mulVec_transpose, h, Matrix.neg_mulVec,
    neg_dotProduct, neg_neg, dotProduct_comm]

theorem d2v_riemannReal_self (hA : Aᵀ = -A) (s : Fin n → ℝ) : d2_riemannReal A s s = 0 := by
  have := d2v_riemannReal_swap A hA s s
  linarith

variable {A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ}

theorem d2v_E_J_J (hA : d2_IsRiemannForm P A) (hP : d2_IsPeriodMatrix P) (s t : Fin (2 * g) → ℝ) :
    d2_riemannReal A (d2v_J hP s) (d2v_J hP t) = d2_riemannReal A s t :=
  hA.typeOneOne s t _ _ (d2v_realMap_J hP s) (d2v_realMap_J hP t)

theorem d2v_E_J_right (hA : d2_IsRiemannForm P A) (hP : d2_IsPeriodMatrix P)
    (s t : Fin (2 * g) → ℝ) :
    d2_riemannReal A s (d2v_J hP t) = -d2_riemannReal A (d2v_J hP s) t := by
  have h := d2v_E_J_J hA hP s (d2v_J hP t)
  rw [d2v_J_J, d2v_riemannReal_neg_right] at h
  linarith

theorem d2v_E_pos (hA : d2_IsRiemannForm P A) (hP : d2_IsPeriodMatrix P)
    {s : Fin (2 * g) → ℝ} (hs : s ≠ 0) : 0 < d2_riemannReal A s (d2v_J hP s) :=
  hA.positive s _ hs (d2v_realMap_J hP s)

theorem d2v_det_ne_zero (hA : d2_IsRiemannForm P A) (hP : d2_IsPeriodMatrix P) : A.det ≠ 0 := by
  intro h0
  have h : (A.map (Int.cast : ℤ → ℝ)).det = 0 := by
    rw [show (A.map (Int.cast : ℤ → ℝ)) = (Int.castRingHom ℝ).mapMatrix A from rfl,
      ← RingHom.map_det, h0, map_zero]
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  have := d2v_E_pos hA hP hv
  rw [d2_riemannReal, Matrix.dotProduct_mulVec, hv0, zero_dotProduct] at this
  exact lt_irrefl _ this


section Matrices

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

theorem d2v_neg_inv {K : Type*} [Field K] (M : Matrix (Fin n) (Fin n) K) (h : M.det ≠ 0) :
    (-M)⁻¹ = -M⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [neg_mul_neg, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)]

theorem d2v_detQ (h : A.det ≠ 0) : (A.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
  rw [show (A.map (Int.cast : ℤ → ℚ)) = (Int.castRingHom ℚ).mapMatrix A from rfl,
    ← RingHom.map_det, eq_intCast]
  exact_mod_cast h

theorem d2v_transposeQ (hA : Aᵀ = -A) :
    (A.map (Int.cast : ℤ → ℚ))ᵀ = -A.map (Int.cast : ℤ → ℚ) := by
  rw [← Matrix.transpose_map, hA]
  ext i j; simp

theorem d2v_mul_dualQ (hA : Aᵀ = -A) (h : A.det ≠ 0) :
    A.map (Int.cast : ℤ → ℚ) * (A.map (Int.cast : ℤ → ℚ))⁻¹ᵀ = -1 := by
  rw [Matrix.transpose_nonsing_inv, d2v_transposeQ A hA, d2v_neg_inv _ (d2v_detQ A h),
    Matrix.mul_neg, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (d2v_detQ A h))]

theorem d2v_dualQ_transpose (hA : Aᵀ = -A) (h : A.det ≠ 0) :
    (A.map (Int.cast : ℤ → ℚ))⁻¹ᵀᵀ = -(A.map (Int.cast : ℤ → ℚ))⁻¹ᵀ := by
  rw [Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, d2v_transposeQ A hA,
    d2v_neg_inv _ (d2v_detQ A h), neg_neg]

theorem d2v_map_mul_dual {K : Type*} [Field K] [CharZero K] (hA : Aᵀ = -A) (h : A.det ≠ 0) :
    A.map (Int.cast : ℤ → K) * (A.map (Int.cast : ℤ → ℚ))⁻¹ᵀ.map (Rat.cast : ℚ → K) = -1 := by
  have := congrArg (fun M ↦ (Rat.castHom K).mapMatrix M) (d2v_mul_dualQ A hA h)
  simp only [map_mul, map_neg, map_one] at this
  rw [← this]
  congr 1
  ext i j; simp

theorem d2v_dualForm_apply (x y : Fin n → ℚ) :
    d2_dualForm A x y = x ⬝ᵥ ((A.map (Int.cast : ℤ → ℚ))⁻¹ᵀ *ᵥ y) :=
  Matrix.toBilin'_apply' _ _ _

theorem d2v_dualForm_baseChange_vec (u w : Fin n → ℂ) :
    (d2_dualForm A).baseChange ℂ (d2_vec n u) (d2_vec n w) =
      u ⬝ᵥ ((A.map (Int.cast : ℤ → ℚ))⁻¹ᵀ.map (Rat.cast : ℚ → ℂ) *ᵥ w) := by
  rw [d2v_vec_apply, d2v_vec_apply]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.BilinForm.baseChange_tmul,
    d2v_dualForm_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  simp [Pi.single_apply, Algebra.smul_def]
  ring

end Matrices


section Forms

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)

/-- The complex vector `a + i b` of two real vectors.
Source: Bourbaki, *Algèbre*, ch. II, §5 (complexification `ℝ^n ⊗ ℂ = ℂ^n`). -/
def d2v_cplx (a b : Fin n → ℝ) : Fin n → ℂ := fun l ↦ (a l : ℂ) + Complex.I * (b l : ℂ)

example (a : Fin n → ℝ) : d2v_cplx a 0 = fun l ↦ (a l : ℂ) := by
  funext l; simp [d2v_cplx]

/-- The complex bilinear extension `E_ℂ(x, y) = xᵀ A y` of the form of an integral matrix.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 (the `ℂ`-bilinear
extension of an alternating form). -/
def d2v_EC (x y : Fin n → ℂ) : ℂ := x ⬝ᵥ (A.map (Int.cast : ℤ → ℂ) *ᵥ y)

example (y : Fin n → ℂ) : d2v_EC A 0 y = 0 := zero_dotProduct _

theorem d2v_cplx_eq (a b : Fin n → ℝ) :
    d2v_cplx a b = (fun l ↦ (a l : ℂ)) + Complex.I • fun l ↦ (b l : ℂ) := by
  funext l; simp [d2v_cplx]

theorem d2v_EC_ofReal (a a' : Fin n → ℝ) :
    d2v_EC A (fun l ↦ (a l : ℂ)) (fun l ↦ (a' l : ℂ)) = (d2_riemannReal A a a' : ℂ) := by
  simp only [d2v_EC, d2_riemannReal, Matrix.mulVec, dotProduct, Matrix.map_apply]
  push_cast
  rfl

theorem d2v_EC_cplx (a b a' b' : Fin n → ℝ) :
    d2v_EC A (d2v_cplx a b) (d2v_cplx a' b') =
      ((d2_riemannReal A a a' - d2_riemannReal A b b' : ℝ) : ℂ) +
        Complex.I * ((d2_riemannReal A a b' + d2_riemannReal A b a' : ℝ) : ℂ) := by
  have h : ∀ x y z : Fin n → ℂ, d2v_EC A (x + y) z = d2v_EC A x z + d2v_EC A y z :=
    fun _ _ _ ↦ add_dotProduct _ _ _
  have h' : ∀ x y z : Fin n → ℂ, d2v_EC A x (y + z) = d2v_EC A x y + d2v_EC A x z :=
    fun _ _ _ ↦ by simp [d2v_EC, Matrix.mulVec_add, dotProduct_add]
  have hs : ∀ (c : ℂ) (x y : Fin n → ℂ), d2v_EC A (c • x) y = c * d2v_EC A x y :=
    fun _ _ _ ↦ by simp [d2v_EC, smul_dotProduct]
  have hs' : ∀ (c : ℂ) (x y : Fin n → ℂ), d2v_EC A x (c • y) = c * d2v_EC A x y :=
    fun _ _ _ ↦ by simp [d2v_EC, Matrix.mulVec_smul, dotProduct_smul]
  rw [d2v_cplx_eq, d2v_cplx_eq, h, h', h', hs, hs, hs', hs', d2v_EC_ofReal, d2v_EC_ofReal,
    d2v_EC_ofReal, d2v_EC_ofReal]
  push_cast
  linear_combination (d2_riemannReal A b b' : ℂ) * Complex.I_mul_I

theorem d2v_transpose_mulVec_cplx (a b : Fin n → ℝ) (k : Fin n) :
    ((A.map (Int.cast : ℤ → ℂ))ᵀ *ᵥ d2v_cplx a b) k =
      (d2_riemannReal A a (Pi.single k 1) : ℂ) +
        Complex.I * (d2_riemannReal A b (Pi.single k 1) : ℂ) := by
  have h1 : ((A.map (Int.cast : ℤ → ℂ))ᵀ *ᵥ d2v_cplx a b) k =
      d2v_EC A (d2v_cplx a b) (d2v_cplx (Pi.single k 1) 0) := by
    have he : d2v_cplx (Pi.single k 1 : Fin n → ℝ) 0 = Pi.single k 1 := by
      funext l; by_cases hl : l = k
      · subst hl; simp [d2v_cplx]
      · simp [d2v_cplx, hl]
    rw [he, d2v_EC, Matrix.dotProduct_mulVec, dotProduct_single_one, Matrix.mulVec_transpose]
  rw [h1, d2v_EC_cplx]
  simp [d2_riemannReal]


theorem d2v_ARc_transpose (hA : Aᵀ = -A) :
    (A.map (Int.cast : ℤ → ℂ))ᵀ = -A.map (Int.cast : ℤ → ℂ) := by
  rw [← Matrix.transpose_map, hA]
  ext i j; simp

theorem d2v_dualForm_baseChange_transpose (hA : Aᵀ = -A) (h : A.det ≠ 0) (x y : Fin n → ℂ) :
    (d2_dualForm A).baseChange ℂ (d2_vec n ((A.map (Int.cast : ℤ → ℂ))ᵀ *ᵥ x))
      (d2_vec n ((A.map (Int.cast : ℤ → ℂ))ᵀ *ᵥ y)) = d2v_EC A x y := by
  rw [d2v_dualForm_baseChange_vec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, d2v_map_mul_dual A hA h, Matrix.neg_mulVec, Matrix.one_mulVec,
    d2v_ARc_transpose A hA, Matrix.neg_mulVec, neg_neg]
  rfl

end Forms

section Repr

variable {A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ}

theorem d2v_realMap_single (P : Fin g → Fin (2 * g) → ℂ) (k : Fin (2 * g)) :
    d2_realMap P (Pi.single k 1) = d2_column P k := by
  rw [d2_realMap, Fintype.linearCombination_apply_single, one_smul]

theorem d2v_dual_repr (hA : d2_IsRiemannForm P A) (hP : d2_IsPeriodMatrix P)
    (φ : Module.Dual ℂ (Fin g → ℂ)) : ∃ t : Fin (2 * g) → ℝ, ∀ s,
      φ (d2_realMap P s) = (d2_riemannReal A t s : ℂ) +
        Complex.I * (d2_riemannReal A (d2v_J hP t) s : ℂ) := by
  have hdet := d2v_det_ne_zero hA hP
  let r : Fin (2 * g) → ℝ := fun k ↦ (φ (d2_column P k)).re
  let t := (A.map (Int.cast : ℤ → ℚ))⁻¹ᵀ.map (Rat.cast : ℚ → ℝ) *ᵥ r
  have hAR : (A.map (Int.cast : ℤ → ℝ))ᵀ = -A.map (Int.cast : ℤ → ℝ) := by
    rw [← Matrix.transpose_map, hA.alternating]
    ext i j; simp
  have hEt : ∀ s, d2_riemannReal A t s = r ⬝ᵥ s := by
    intro s
    rw [d2_riemannReal, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hAR,
      Matrix.neg_mulVec, Matrix.mulVec_mulVec, d2v_map_mul_dual A hA.alternating hdet,
      Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]
  have hre : ∀ s, (φ (d2_realMap P s)).re = r ⬝ᵥ s := by
    intro s
    have h := d2v_apply_realMap P (φ.restrictScalars ℝ) s
    simp only [LinearMap.restrictScalars_apply] at h
    rw [h, Complex.re_sum, dotProduct]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Complex.real_smul, Complex.re_ofReal_mul, mul_comm]
  refine ⟨t, fun s ↦ Complex.ext ?_ ?_⟩
  · simp [hre, hEt]
  · have h1 : (φ (d2_realMap P s)).im = (φ (d2_realMap P (-(d2v_J hP s)))).re := by
      rw [map_neg, d2v_realMap_J, map_neg, map_smul, smul_eq_mul]
      simp
    rw [h1, hre, ← hEt, d2v_riemannReal_neg_right, d2v_E_J_right hA hP]
    simp

end Repr


section Polarized

variable {A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ}

theorem d2v_mem_hodgeOne_repr (hA : d2_IsRiemannForm P A) (hP : d2_IsPeriodMatrix P)
    {x : ℂ ⊗[ℚ] (Fin (2 * g) → ℚ)} (hx : x ∈ d2_hodgeOne P) : ∃ t : Fin (2 * g) → ℝ,
      x = d2_vec _ ((A.map (Int.cast : ℤ → ℂ))ᵀ *ᵥ d2v_cplx t (d2v_J hP t)) := by
  obtain ⟨φ, rfl⟩ := hx
  obtain ⟨t, ht⟩ := d2v_dual_repr hA hP φ
  refine ⟨t, ?_⟩
  show d2_vec _ _ = _
  congr 1
  funext k
  rw [d2v_transpose_mulVec_cplx, ← ht, d2v_realMap_single]
  rfl

theorem d2v_sigmaQ_repr (hP : d2_IsPeriodMatrix P) (t : Fin (2 * g) → ℝ) :
    sigmaQ _ (d2_vec _ ((A.map (Int.cast : ℤ → ℂ))ᵀ *ᵥ d2v_cplx t (d2v_J hP t))) =
      d2_vec _ ((A.map (Int.cast : ℤ → ℂ))ᵀ *ᵥ d2v_cplx t (-d2v_J hP t)) := by
  rw [d2v_sigmaQ_vec]
  congr 1
  funext k
  rw [d2v_transpose_mulVec_cplx, d2v_transpose_mulVec_cplx, d2v_riemannReal_neg_left]
  simp [Complex.conj_ofReal]

theorem d2v_repr_ne_zero (hP : d2_IsPeriodMatrix P) {t : Fin (2 * g) → ℝ}
    (h : d2_vec _ ((A.map (Int.cast : ℤ → ℂ))ᵀ *ᵥ d2v_cplx t (d2v_J hP t)) ≠ 0) : t ≠ 0 := by
  rintro rfl
  apply h
  have : d2v_cplx (0 : Fin (2 * g) → ℝ) (d2v_J hP 0) = 0 := by
    funext l; simp [d2v_cplx]
  rw [this, Matrix.mulVec_zero, map_zero]

theorem d2v_filtration_isPolarized (hA : d2_IsRiemannForm P A) :
    d1_IsPolarizedFiltration 1 (d2_dualForm A) (d2_filtration P) := by
  have hP := d2_isPeriodMatrix_of_isRiemannForm_aux hA
  have hdet := d2v_det_ne_zero hA hP
  have halt := hA.alternating
  have hQ := d2v_detQ A hdet
  have hEC : ∀ t t' : Fin (2 * g) → ℝ, (d2_dualForm A).baseChange ℂ
      (d2_vec _ ((A.map (Int.cast : ℤ → ℂ))ᵀ *ᵥ d2v_cplx t (d2v_J hP t)))
      (d2_vec _ ((A.map (Int.cast : ℤ → ℂ))ᵀ *ᵥ d2v_cplx t' (d2v_J hP t'))) = 0 := by
    intro t t'
    rw [d2v_dualForm_baseChange_transpose A halt hdet, d2v_EC_cplx, d2v_E_J_J hA hP,
      d2v_E_J_right hA hP]
    simp
  have hF1 : ∀ x, x ∈ d2_filtration P 1 ↔ x ∈ d2_hodgeOne P := fun x ↦ by
    simp [d2_filtration]
  refine ⟨d2v_filtration_isHodge hP, ?_, ?_, ?_, ?_⟩
  · rw [d2_dualForm, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero, Matrix.det_transpose]
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr hQ)).ne_zero
  · intro x y
    rw [d2v_dualForm_apply, d2v_dualForm_apply, zpow_one, Matrix.dotProduct_mulVec y,
      ← Matrix.mulVec_transpose, d2v_dualQ_transpose A halt hdet, Matrix.neg_mulVec,
      neg_dotProduct, dotProduct_comm]
    ring
  · intro p x hx y hy
    rcases lt_trichotomy p 1 with hp | rfl | hp
    · rw [d2v_mem_filtration_le P _ y hy (by omega), map_zero]
    · obtain ⟨t, rfl⟩ := d2v_mem_hodgeOne_repr hA hP ((hF1 _).mp hx)
      obtain ⟨t', rfl⟩ := d2v_mem_hodgeOne_repr hA hP ((hF1 _).mp hy)
      exact hEC t t'
    · rw [d2v_mem_filtration_le P _ x hx (by omega), map_zero, LinearMap.zero_apply]
  · intro p q hpq x hx hx0
    simp only [d1_hodgePiece, hpq, ite_true, Submodule.mem_inf] at hx
    obtain ⟨hxp, hxq⟩ := hx
    rcases lt_trichotomy p 0 with hp | rfl | hp
    · exfalso; apply hx0
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hxq
      rw [d2v_mem_filtration_le P _ y hy (by omega), map_zero]
    · obtain rfl : q = 1 := by omega
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hxq
      obtain ⟨t, rfl⟩ := d2v_mem_hodgeOne_repr hA hP ((hF1 _).mp hy)
      have ht := d2v_E_pos hA hP (d2v_repr_ne_zero hP fun h ↦ hx0 (by rw [h, map_zero]))
      rw [sigmaQ_involutive, d2v_sigmaQ_repr, d2v_dualForm_baseChange_transpose A halt hdet,
        d2v_EC_cplx, d2v_riemannReal_neg_left, d2v_riemannReal_neg_left,
        d2v_riemannReal_self A halt, d2v_riemannReal_self A halt (d2v_J hP t),
        d2v_riemannReal_swap A halt (d2v_J hP t) t]
      have hI : Iexp (0 - 1) = -Complex.I := by
        rw [Iexp, zero_sub, zpow_neg, zpow_one, Complex.inv_I]
      rw [hI]
      simp [Complex.mul_re]
      linarith
    · obtain rfl : p = 1 := by
        by_contra h
        apply hx0
        exact d2v_mem_filtration_le P _ x hxp (by omega)
      obtain rfl : q = 0 := by omega
      obtain ⟨t, rfl⟩ := d2v_mem_hodgeOne_repr hA hP ((hF1 _).mp hxp)
      have ht := d2v_E_pos hA hP (d2v_repr_ne_zero hP hx0)
      rw [d2v_sigmaQ_repr, d2v_dualForm_baseChange_transpose A halt hdet, d2v_EC_cplx,
        d2v_riemannReal_neg_right, d2v_riemannReal_neg_right, d2v_riemannReal_self A halt,
        d2v_riemannReal_swap A halt (d2v_J hP t) t]
      rw [d2v_riemannReal_self A halt (d2v_J hP t)]
      have hI : Iexp (1 - 0) = Complex.I := by simp [Iexp]
      rw [hI]
      simp [Complex.mul_re]
      linarith

end Polarized

end HodgeLean.Foundations.Program
