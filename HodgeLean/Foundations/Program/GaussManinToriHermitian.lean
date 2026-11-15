import HodgeLean.Foundations.Program.GaussManinToriDefs
import HodgeLean.Foundations.Program.GaussManinToriLatticeProofs
import HodgeLean.Foundations.AppellHumbert

/-!
# Period matrices: coordinates of Riemann forms and Hermitian forms

Helper lemmas for `GaussManinToriProofs.lean`: the real map of a period matrix is the coordinate
isomorphism of the column basis, the real extension of an integral form is bilinear and
alternating when the matrix is, and the imaginary part of a `HermitianForm` is antisymmetric and
invariant under `i`. Also the coordinate vector `(a, b)` of `ℂ ⊗ ℚ²`.

HC no distance; AV milestone no distance.
-/

noncomputable section

open scoped TensorProduct Matrix

namespace HodgeLean.Foundations.Program

open HodgeLean.Foundations.AppellHumbert

variable {g : ℕ} {P : Fin g → Fin (2 * g) → ℂ}

/-- The real map of a period matrix is the inverse coordinate map of its column basis. -/
theorem d2l_realMap_eq (hP : d2_IsPeriodMatrix P) (s : Fin (2 * g) → ℝ) :
    d2_realMap P s = (d2l_basis hP).equivFun.symm s := by
  rw [Module.Basis.equivFun_symm_apply, d2l_basis_coe, d2_realMap,
    Fintype.linearCombination_apply]

/-- The real map of a period matrix is injective. -/
theorem d2l_realMap_injective (hP : d2_IsPeriodMatrix P) : Function.Injective (d2_realMap P) :=
  (linearIndependent_iff_injective_fintypeLinearCombination).1 hP

/-- The real extension of an integral form is additive on the left. -/
theorem d2l_riemannReal_add_left {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (s s' t : Fin n → ℝ) :
    d2_riemannReal A (s + s') t = d2_riemannReal A s t + d2_riemannReal A s' t :=
  add_dotProduct _ _ _

/-- The real extension of an integral form is homogeneous on the left. -/
theorem d2l_riemannReal_smul_left {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (r : ℝ)
    (s t : Fin n → ℝ) :
    d2_riemannReal A (r • s) t = r * d2_riemannReal A s t :=
  smul_dotProduct _ _ _

/-- The real extension of an integral form is additive on the right. -/
theorem d2l_riemannReal_add_right {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (s t t' : Fin n → ℝ) :
    d2_riemannReal A s (t + t') = d2_riemannReal A s t + d2_riemannReal A s t' := by
  rw [d2_riemannReal, Matrix.mulVec_add, dotProduct_add]; rfl

/-- The real extension of an integral form is homogeneous on the right. -/
theorem d2l_riemannReal_smul_right {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (r : ℝ)
    (s t : Fin n → ℝ) :
    d2_riemannReal A s (r • t) = r * d2_riemannReal A s t := by
  rw [d2_riemannReal, Matrix.mulVec_smul, dotProduct_smul]; rfl

/-- The real extension of an alternating integral matrix vanishes on the diagonal. -/
theorem d2l_riemannReal_self {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : Aᵀ = -A)
    (s : Fin n → ℝ) : d2_riemannReal A s s = 0 := by
  have hM : (A.map (Int.cast : ℤ → ℝ))ᵀ = -A.map (Int.cast : ℤ → ℝ) := by
    rw [← Matrix.transpose_map, hA, Matrix.map_neg _ Int.cast_neg]
  have h : d2_riemannReal A s s = ((A.map (Int.cast : ℤ → ℝ))ᵀ *ᵥ s) ⬝ᵥ s := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]; rfl
  rw [hM, Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm] at h
  change d2_riemannReal A s s = -d2_riemannReal A s s at h
  linarith

/-- The real extension on two basis vectors is the matrix entry. -/
theorem d2l_riemannReal_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    d2_riemannReal A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [d2_riemannReal]

/-- The imaginary part of a Hermitian form is invariant under `i`. -/
theorem d2l_imaginary_I_I (H : HermitianForm (V := Fin g → ℂ)) (v w : Fin g → ℂ) :
    H.imaginary (Complex.I • v) (Complex.I • w) = H.imaginary v w := by
  simp [HermitianForm.imaginary, H.smul_left, H.smul_right, ← mul_assoc]

/-- `Im H(v, i v) = Re H(v, v)`, the repository's sign convention. -/
theorem d2l_imaginary_I_right (H : HermitianForm (V := Fin g → ℂ)) (v : Fin g → ℂ) :
    H.imaginary v (Complex.I • v) = (H.toFun v v).re := by
  simp [HermitianForm.imaginary, H.smul_right]

/-- The imaginary part of a Hermitian form is antisymmetric. -/
theorem d2l_imaginary_swap (H : HermitianForm (V := Fin g → ℂ)) (v w : Fin g → ℂ) :
    H.imaginary w v = -H.imaginary v w := by
  rw [HermitianForm.imaginary, HermitianForm.imaginary, ← H.conj_symm v w]
  simp

/-- The coordinate vector `(a, b)` of `ℂ ⊗ ℚ²`. -/
theorem d2l_vec_two (a b : ℂ) :
    d2_vec 2 ![a, b] = a ⊗ₜ Pi.single 0 1 + b ⊗ₜ Pi.single 1 1 := by
  simp [d2_vec, Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, Module.Basis.baseChange_apply,
    TensorProduct.smul_tmul']

end HodgeLean.Foundations.Program
