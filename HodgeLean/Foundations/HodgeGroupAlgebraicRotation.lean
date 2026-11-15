import HodgeLean.Foundations.HodgeGroupAlgebraicBridge

/-! # Track G2: the rotation structure on `ℚ²`

For the weight-one structure of the rotation `[[0, -1], [1, 0]]`, the circle acts by the real
rotation matrices `[[Re z, Im z], [-Im z, Re z]]`, and a polynomial vanishing on them vanishes on
every complex matrix `[[a, c], [-c, a]]` with `a² + c² = 1`.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations

open MvPolynomial
open scoped TensorProduct

theorem g2b_circleAction_rotation
    (hH : DirectSum.IsInternal (complexStructureHodge rotation 1 0)) (z : Circle) :
    g2_circleAction (complexStructureHodge rotation 1 0) hH z =
      ((z : ℂ).re : ℂ) • LinearMap.id - ((z : ℂ).im : ℂ) • rotation.baseChange ℂ := by
  refine linearMap_ext_of_isInternal hH fun k x hx => ?_
  rw [g2_circleAction_apply_of_mem _ hH z hx]
  simp only [complexStructureHodge] at hx
  split_ifs at hx with h1 h2
  · subst h1
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      Module.End.mem_eigenspace_iff.mp hx, LinearMap.id_apply, smul_smul, ← sub_smul]
    congr 1
    conv_lhs => rw [← Complex.re_add_im (z : ℂ)]
    simp
  · subst h2
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      Module.End.mem_eigenspace_iff.mp hx, LinearMap.id_apply, smul_smul, ← sub_smul]
    congr 1
    rw [show ((0 : ℤ) - 1) = -1 by norm_num, zpow_neg_one, ← Circle.coe_inv, Circle.coe_inv_eq_conj]
    conv_lhs => rw [← Complex.re_add_im (z : ℂ)]
    apply Complex.ext <;> simp
  · rw [(Submodule.mem_bot ℂ).mp hx]
    simp

theorem g2b_toMatrix_rotation :
    LinearMap.toMatrix (Pi.basisFun ℚ (Fin 2)) (Pi.basisFun ℚ (Fin 2)) rotation =
      !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation_single_zero, rotation_single_one]

theorem g2b_toMatrix_circleAction_rotation
    (hH : DirectSum.IsInternal (complexStructureHodge rotation 1 0)) (z : Circle) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ (Pi.basisFun ℚ (Fin 2)))
        (Algebra.TensorProduct.basis ℂ (Pi.basisFun ℚ (Fin 2)))
        (g2_circleAction (complexStructureHodge rotation 1 0) hH z) =
      !![((z : ℂ).re : ℂ), ((z : ℂ).im : ℂ); -((z : ℂ).im : ℂ), ((z : ℂ).re : ℂ)] := by
  rw [g2b_circleAction_rotation, map_sub, map_smul, map_smul, LinearMap.toMatrix_id,
    LinearMap.toMatrix_baseChange, g2b_toMatrix_rotation]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem g2b_circle_infinite : Set.Infinite {w : ℂ | ∃ z : Circle, (z : ℂ) = w} := by
  have hinj : Set.InjOn (fun t : ℝ => (Circle.exp t : ℂ)) (Set.Ioo 0 Real.pi) :=
    fun s hs t ht hst => Real.injOn_cos ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩ (by
      have := congrArg Complex.re hst
      simpa [Circle.coe_exp, Complex.exp_ofReal_mul_I_re] using this)
  exact ((Set.Ioo_infinite Real.pi_pos).image hinj).mono (by
    rintro _ ⟨t, -, rfl⟩
    exact ⟨_, rfl⟩)

/-- A polynomial in the matrix entries, evaluated at entries of the form `α w + β w⁻¹`, is
`w^(-N)` times a polynomial in `w`. -/
theorem g2b_exists_laurent {σ : Type*} (α β : σ → ℂ) (f : MvPolynomial σ ℂ) :
    ∃ N : ℕ, ∃ h : Polynomial ℂ, ∀ w : ℂ, w ≠ 0 →
      w ^ N * eval (fun ij => α ij * w + β ij * w⁻¹) f = h.eval w := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, Polynomial.C a, fun w _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨N₁, h₁, hh₁⟩ := hp
    obtain ⟨N₂, h₂, hh₂⟩ := hq
    refine ⟨N₁ + N₂, h₁ * Polynomial.X ^ N₂ + h₂ * Polynomial.X ^ N₁, fun w hw => ?_⟩
    simp only [map_add, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, ← hh₁ w hw, ← hh₂ w hw]
    ring
  | mul_X p i hp =>
    obtain ⟨N, h, hh⟩ := hp
    refine ⟨N + 1, h * (Polynomial.C (α i) * Polynomial.X ^ 2 + Polynomial.C (β i)),
      fun w hw => ?_⟩
    simp only [map_mul, eval_X, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, ← hh w hw]
    have key : w * (α i * w + β i * w⁻¹) = α i * w ^ 2 + β i := by
      field_simp
    linear_combination (w ^ N * eval (fun ij => α ij * w + β ij * w⁻¹) p) * key

/-- A polynomial vanishing at the entries `α z + β z⁻¹` for every `z` on the unit circle
vanishes at `α w + β w⁻¹` for every `w ≠ 0`. -/
theorem g2b_eval_eq_zero_of_circle {σ : Type*} (α β : σ → ℂ) (f : MvPolynomial σ ℂ)
    (hf : ∀ z : Circle, eval (fun ij => α ij * (z : ℂ) + β ij * (z : ℂ)⁻¹) f = 0)
    {w : ℂ} (hw : w ≠ 0) : eval (fun ij => α ij * w + β ij * w⁻¹) f = 0 := by
  obtain ⟨N, h, hh⟩ := g2b_exists_laurent α β f
  have h0 : h = 0 := Polynomial.eq_zero_of_infinite_isRoot h (g2b_circle_infinite.mono (by
    rintro _ ⟨z, rfl⟩
    change h.eval (z : ℂ) = 0
    rw [← hh _ (Circle.coe_ne_zero z), hf z, mul_zero]))
  have := hh w hw
  rw [h0, Polynomial.eval_zero] at this
  exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hw)

/-- The matrix `[[a, c], [-c, a]]` with `a = (w + w⁻¹)/2`, `c = (w - w⁻¹)/(2i)`: the complex
rotation of parameter `w ≠ 0`, of determinant `a² + c² = 1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.5 (the torus `SO(2)` and its character
`w`); Moonen, *An introduction to Mumford–Tate groups* (2004), §1–2 (CM elliptic curves). -/
def g2b_rotMatrix (w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(w + w⁻¹) / 2, (w - w⁻¹) / (2 * Complex.I); -((w - w⁻¹) / (2 * Complex.I)), (w + w⁻¹) / 2]

example : g2b_rotMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g2b_rotMatrix]

theorem g2b_det_rotMatrix {w : ℂ} (hw : w ≠ 0) : (g2b_rotMatrix w).det = 1 := by
  rw [g2b_rotMatrix, Matrix.det_fin_two_of]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  field_simp
  ring

/-- The complex rotation of parameter `w ≠ 0` as an element of `GL₂(ℂ)`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.5; Bourbaki, *Algèbre*, ch. III, §8
(invertibility of a matrix of determinant `1`). -/
def g2b_rotGL {w : ℂ} (hw : w ≠ 0) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (g2b_rotMatrix w) (by
    rw [g2b_det_rotMatrix hw]; exact one_ne_zero)

example : (g2b_rotGL (one_ne_zero : (1 : ℂ) ≠ 0) : Matrix (Fin 2) (Fin 2) ℂ).det = 1 :=
  g2b_det_rotMatrix one_ne_zero

theorem g2b_coe_rotGL {w : ℂ} (hw : w ≠ 0) :
    ((g2b_rotGL hw : Matrix.GeneralLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      g2b_rotMatrix w := rfl

/-- The coefficients of `w` in the entries of `g2b_rotMatrix w`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.5 (coordinates of `SO(2)` in the
character `w`). -/
def g2b_rotα : Fin 2 × Fin 2 → ℂ := fun ij =>
  !![1 / 2, 1 / (2 * Complex.I); -(1 / (2 * Complex.I)), 1 / 2] ij.1 ij.2

example : g2b_rotα (0, 0) = 1 / 2 := by simp [g2b_rotα]

/-- The coefficients of `w⁻¹` in the entries of `g2b_rotMatrix w`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §8.5. -/
def g2b_rotβ : Fin 2 × Fin 2 → ℂ := fun ij =>
  !![1 / 2, -(1 / (2 * Complex.I)); 1 / (2 * Complex.I), 1 / 2] ij.1 ij.2

example : g2b_rotβ (1, 1) = 1 / 2 := by simp [g2b_rotβ]

theorem g2b_coords_rotGL {w : ℂ} (hw : w ≠ 0) :
    g1_coords (g2b_rotGL hw) = fun ij => g2b_rotα ij * w + g2b_rotβ ij * w⁻¹ := by
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [g1_coords, g2b_coe_rotGL, g2b_rotMatrix, g2b_rotα, g2b_rotβ] <;> ring_nf <;> simp only [Complex.inv_I] <;> ring

/-- On the unit circle, `g2b_rotMatrix z` is the real rotation `[[Re z, Im z], [-Im z, Re z]]`. -/
theorem g2b_rotMatrix_circle (z : Circle) :
    g2b_rotMatrix (z : ℂ) =
      !![((z : ℂ).re : ℂ), ((z : ℂ).im : ℂ); -((z : ℂ).im : ℂ), ((z : ℂ).re : ℂ)] := by
  rw [g2b_rotMatrix, Complex.re_eq_add_conj, Complex.im_eq_sub_conj, ← Circle.coe_inv_eq_conj,
    Circle.coe_inv]

section Rotation

variable (hH : DirectSum.IsInternal (complexStructureHodge rotation 1 0))

theorem g2b_rotGL_mem_circleImage (z : Circle) :
    g2b_rotGL (Circle.coe_ne_zero z) ∈
      g2_circleImage (complexStructureHodge rotation 1 0) hH (Pi.basisFun ℚ (Fin 2)) :=
  ⟨z, by rw [g2b_coe_rotGL, g2b_rotMatrix_circle, g2b_toMatrix_circleAction_rotation]⟩

/-- A zero set of rational polynomials containing the real rotations contains every complex
rotation. -/
theorem g2b_rotGL_mem_of_circleImage_subset {S : Set (MvPolynomial (Fin 2 × Fin 2) ℚ)}
    (hS : g2_circleImage (complexStructureHodge rotation 1 0) hH (Pi.basisFun ℚ (Fin 2)) ⊆
      g2_ratZeroSet S) {w : ℂ} (hw : w ≠ 0) : g2b_rotGL hw ∈ g2_ratZeroSet S := by
  intro f hf
  rw [g2b_aeval_eq_eval_map, g2b_coords_rotGL]
  refine g2b_eval_eq_zero_of_circle _ _ _ (fun z => ?_) hw
  have := hS (g2b_rotGL_mem_circleImage hH z) f hf
  rwa [g2b_aeval_eq_eval_map, g2b_coords_rotGL] at this

end Rotation

/-- The complex points of `SO(2)`: `[[a, c], [-c, a]]` with determinant `1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6 (classical groups) and §8.5. -/
def g2b_SO2 : Set (Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
  {g : Matrix.GeneralLinearGroup (Fin 2) ℂ | (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
    (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ∧
    (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = -(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ∧
    (g : Matrix (Fin 2) (Fin 2) ℂ).det = 1}

example : (1 : Matrix.GeneralLinearGroup (Fin 2) ℂ) ∈ g2b_SO2 := by simp [g2b_SO2]

theorem g2b_eq_rotGL_of_mem_SO2 {g : Matrix.GeneralLinearGroup (Fin 2) ℂ} (hg : g ∈ g2b_SO2) :
    ∃ (w : ℂ) (hw : w ≠ 0), g = g2b_rotGL hw := by
  obtain ⟨h1, h2, h3⟩ := hg
  set a := (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
  set c := (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
  rw [Matrix.det_fin_two] at h3
  have hmul : (a + Complex.I * c) * (a - Complex.I * c) = 1 := by
    rw [← h3, ← h1]
    linear_combination c * h2 - c ^ 2 * Complex.I_sq
  have hw : a + Complex.I * c ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hinv : (a + Complex.I * c)⁻¹ = a - Complex.I * c := inv_eq_of_mul_eq_one_right hmul
  refine ⟨_, hw, Units.ext ?_⟩
  rw [g2b_coe_rotGL, g2b_rotMatrix, hinv]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one]
    ring
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    field_simp
    ring
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one]
    rw [← neg_neg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0), ← h2]
    field_simp
    ring
  · simp only [Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [← h1]
    ring

theorem g2b_rotGL_mem_SO2 {w : ℂ} (hw : w ≠ 0) : g2b_rotGL hw ∈ g2b_SO2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [g2b_coe_rotGL, g2b_rotMatrix]
  · simp [g2b_coe_rotGL, g2b_rotMatrix]
  · rw [g2b_coe_rotGL, g2b_det_rotMatrix hw]

/-- The rational equations of `SO(2)`: `x₀₀ - x₁₁`, `x₀₁ + x₁₀`, `x₀₀ x₁₁ - x₀₁ x₁₀ - 1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6 (classical groups by equations). -/
def g2b_SO2Equations : Set (MvPolynomial (Fin 2 × Fin 2) ℚ) :=
  {X (0, 0) - X (1, 1), X (0, 1) + X (1, 0), X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0) - 1}

example : X (0, 0) - X (1, 1) ∈ g2b_SO2Equations := Or.inl rfl

theorem g2b_SO2_eq_ratZeroSet : g2b_SO2 = g2_ratZeroSet g2b_SO2Equations := by
  ext g
  simp only [g2b_SO2, g2_ratZeroSet, g2b_SO2Equations, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, map_sub, map_add, map_mul, aeval_X,
    map_one, g1_coords, Matrix.det_fin_two, sub_eq_zero, add_eq_zero_iff_eq_neg]

theorem g2b_isRatAlgSubgroup_SO2 : g2_IsRatAlgSubgroup g2b_SO2 := by
  refine ⟨⟨_, g2b_SO2_eq_ratZeroSet⟩, ?_, ?_, ?_⟩
  · simp [g2b_SO2]
  · intro x hx y hy
    obtain ⟨w, hw, rfl⟩ := g2b_eq_rotGL_of_mem_SO2 hx
    obtain ⟨v, hv, rfl⟩ := g2b_eq_rotGL_of_mem_SO2 hy
    refine ⟨?_, ?_, ?_⟩
    · simp [g2b_coe_rotGL, g2b_rotMatrix, Matrix.mul_apply]
      ring
    · simp [g2b_coe_rotGL, g2b_rotMatrix, Matrix.mul_apply]
    · rw [Units.val_mul, Matrix.det_mul, g2b_coe_rotGL, g2b_coe_rotGL, g2b_det_rotMatrix hw,
        g2b_det_rotMatrix hv, mul_one]
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := hx
    have hinv : ((x⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        (x : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
      rw [Matrix.coe_units_inv, Matrix.inv_def, h3, Ring.inverse_one, one_smul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hinv, Matrix.adjugate_fin_two]
      simp [h1]
    · rw [hinv, Matrix.adjugate_fin_two]
      simp [h2]
    · rw [hinv, Matrix.det_fin_two, Matrix.adjugate_fin_two]
      rw [Matrix.det_fin_two] at h3
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      linear_combination h3

theorem g2b_circleImage_subset_SO2 (hH : DirectSum.IsInternal (complexStructureHodge rotation 1 0)) :
    g2_circleImage (complexStructureHodge rotation 1 0) hH (Pi.basisFun ℚ (Fin 2)) ⊆ g2b_SO2 := by
  rintro g ⟨z, hz⟩
  have : g = g2b_rotGL (Circle.coe_ne_zero z) := by
    ext : 1
    rw [hz, g2b_coe_rotGL, g2b_rotMatrix_circle, g2b_toMatrix_circleAction_rotation]
  rw [this]
  exact g2b_rotGL_mem_SO2 _

/-- **The Hodge group of the rotation structure is `SO(2)`.** -/
theorem g2b_hodgeGroup_rotation (hH : DirectSum.IsInternal (complexStructureHodge rotation 1 0)) :
    g2_hodgeGroup (complexStructureHodge rotation 1 0) hH (Pi.basisFun ℚ (Fin 2)) = g2b_SO2 := by
  refine subset_antisymm
    (Set.sInter_subset_of_mem ⟨g2b_isRatAlgSubgroup_SO2, g2b_circleImage_subset_SO2 hH⟩) ?_
  intro g hg G ⟨⟨⟨S, hS⟩, _⟩, hc⟩
  obtain ⟨w, hw, rfl⟩ := g2b_eq_rotGL_of_mem_SO2 hg
  rw [hS] at hc ⊢
  exact g2b_rotGL_mem_of_circleImage_subset hH hc hw

/-- **The bare circle image of the rotation structure is not `ℚ`-algebraic**: the complex rotation
of parameter `2` has entry `5/4`, which is not the real part of a unit complex number. -/
theorem g2b_not_isRatAlgSubgroup_circleImage
    (hH : DirectSum.IsInternal (complexStructureHodge rotation 1 0)) :
    ¬ g2_IsRatAlgSubgroup
      (g2_circleImage (complexStructureHodge rotation 1 0) hH (Pi.basisFun ℚ (Fin 2))) := by
  rintro ⟨⟨S, hS⟩, -⟩
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hmem := g2b_rotGL_mem_of_circleImage_subset hH hS.subset h2
  rw [← hS] at hmem
  obtain ⟨z, hz⟩ := hmem
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hz
  simp only [g2b_coe_rotGL, g2b_rotMatrix, g2b_toMatrix_circleAction_rotation] at h00
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    at h00
  have hre : (z : ℂ).re = 5 / 4 := by
    have := congrArg Complex.re h00
    norm_num at this
    linarith
  have hle := Complex.re_le_norm (z : ℂ)
  rw [Circle.norm_coe, hre] at hle
  norm_num at hle

section Gk

variable {n : ℕ}

theorem g2b_mapMatrix_aeval_varMatrix (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    (aeval (g1_coords g)).mapMatrix (g1_varMatrix ℚ n) = (g : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  simp [g1_varMatrix, g1_coords]

theorem g2b_mapMatrix_aeval_map_C (g : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℚ) :
    (aeval (g1_coords g)).mapMatrix (M.map C) = M.map (algebraMap ℚ ℂ) := by
  ext i j
  simp

theorem g2b_aeval_commEquations (g : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    aeval (g1_coords g) (g2_commEquations M i j) =
      ((g : Matrix (Fin n) (Fin n) ℂ) * M.map (algebraMap ℚ ℂ) -
        M.map (algebraMap ℚ ℂ) * (g : Matrix (Fin n) (Fin n) ℂ)) i j := by
  change (aeval (g1_coords g)).mapMatrix (g2_commEquations M) i j = _
  rw [g2_commEquations, map_sub, map_mul, map_mul, g2b_mapMatrix_aeval_varMatrix,
    g2b_mapMatrix_aeval_map_C]

theorem g2b_aeval_isometryEquations (g : Matrix.GeneralLinearGroup (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    aeval (g1_coords g) (g1_isometryEquations M i j) =
      (Matrix.transpose (g : Matrix (Fin n) (Fin n) ℂ) * M.map (algebraMap ℚ ℂ) *
        (g : Matrix (Fin n) (Fin n) ℂ) -
        M.map (algebraMap ℚ ℂ)) i j := by
  change (aeval (g1_coords g)).mapMatrix (g1_isometryEquations M) i j = _
  rw [g1_isometryEquations, map_sub, map_mul, map_mul, g2b_mapMatrix_aeval_map_C]
  have hT : (aeval (g1_coords g)).mapMatrix (Matrix.transpose (g1_varMatrix ℚ n)) =
      Matrix.transpose (g : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← g2b_mapMatrix_aeval_varMatrix g]
    rfl
  rw [hT, g2b_mapMatrix_aeval_varMatrix]

theorem g2b_aeval_det_varMatrix (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    aeval (g1_coords g) (g1_varMatrix ℚ n).det = (g : Matrix (Fin n) (Fin n) ℂ).det := by
  rw [AlgHom.map_det, g2b_mapMatrix_aeval_varMatrix]

end Gk

theorem g2b_kDetTrace_rotation :
    g2_kDetTrace (Pi.basisFun ℚ (Fin 2)) rotation 1 = X (0, 0) + X (1, 1) := by
  have h : ((g2_kCharPoly (Pi.basisFun ℚ (Fin 2)) rotation).coeff 0).coeff 1 =
      X (0, 0) + X (1, 1) := by
    rw [g2_kCharPoly, Matrix.det_fin_two, Polynomial.coeff_zero_eq_eval_zero]
    simp [g1_varMatrix]
    rw [show ∀ a b : MvPolynomial (Fin 2 × Fin 2) ℚ, (Polynomial.C a + Polynomial.X) *
        (Polynomial.C b + Polynomial.X) =
        Polynomial.X ^ 2 + Polynomial.C (a + b) * Polynomial.X + Polynomial.C (a * b) from
      fun a b => by simp only [map_add, map_mul]; ring]
    simp [Polynomial.coeff_C]
  simp [g2_kDetTrace, h]

/-- **`G_k` of the rotation structure is trivial.** -/
theorem g2b_gkGroup_rotation :
    g2_gkGroup (Pi.basisFun ℚ (Fin 2)) (Matrix.toBilin' !![0, 1; -1, 0])
        (Algebra.adjoin ℚ {rotation}) rotation 1 = {1} := by
  ext g
  rw [Set.mem_singleton_iff]
  constructor
  · intro hg
    have hc : ∀ i j, ((g : Matrix (Fin 2) (Fin 2) ℂ) *
        (LinearMap.toMatrix (Pi.basisFun ℚ (Fin 2)) (Pi.basisFun ℚ (Fin 2)) rotation).map
          (algebraMap ℚ ℂ) -
        (LinearMap.toMatrix (Pi.basisFun ℚ (Fin 2)) (Pi.basisFun ℚ (Fin 2)) rotation).map
          (algebraMap ℚ ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)) i j = 0 := fun i j => by
      rw [← g2b_aeval_commEquations]
      exact hg _ (Or.inl (Or.inl (Or.inr ⟨i, j, rfl⟩)))
    have hdet := hg _ (Or.inr (Or.inl rfl))
    have htr := hg _ (Or.inr (Or.inr rfl))
    rw [map_sub, map_one, g2b_aeval_det_varMatrix, Matrix.det_fin_two, sub_eq_zero] at hdet
    rw [g2b_kDetTrace_rotation, map_sub, map_add, aeval_X, aeval_X, sub_eq_zero] at htr
    have h00 := hc 0 0
    have h01 := hc 0 1
    rw [g2b_toMatrix_rotation] at h00 h01
    simp [Matrix.mul_apply] at h00 h01
    simp only [g1_coords, map_ofNat] at htr
    have ha : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := by linear_combination htr / 2 - h01 / 2
    have hd : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 1 := by linear_combination htr / 2 + h01 / 2
    have hb : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
      have : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ^ 2 = 0 := by
        linear_combination hdet + (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * h00 -
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * ha - hd
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    have hc' : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by linear_combination h00 - hb
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc', hd]
  · rintro rfl f hf
    rcases hf with ((⟨r, -, i, j, rfl⟩ | ⟨i, j, rfl⟩) | ⟨i, j, rfl⟩) | rfl | rfl
    · rw [g2b_aeval_commEquations]
      simp
    · rw [g2b_aeval_commEquations]
      simp
    · rw [g2b_aeval_isometryEquations]
      simp
    · rw [map_sub, map_one, g2b_aeval_det_varMatrix]
      simp
    · rw [g2b_kDetTrace_rotation, map_sub, map_add, aeval_X, aeval_X]
      simp [g1_coords]
      norm_num

end HodgeLean.Foundations
