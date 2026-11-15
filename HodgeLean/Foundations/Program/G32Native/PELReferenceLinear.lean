import HodgeLean.Foundations.Program.G32Native.PELSplitReference
import HodgeLean.Foundations.PositivePolarizationRosati
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section
open scoped TensorProduct
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

variable {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]

/-- Scalar extension of the matrix of a rational bilinear form. -/
theorem pel_form_matrix_real (b : Module.Basis ι ℚ V) (E : LinearMap.BilinForm ℚ V) :
    LinearMap.toMatrix₂ (Algebra.TensorProduct.basis ℝ b)
      (Algebra.TensorProduct.basis ℝ b) (E.baseChange ℝ) =
      (LinearMap.toMatrix₂ b b E).map (algebraMap ℚ ℝ) := by
  ext i j
  simp [LinearMap.toMatrix₂_apply]

/-- A real operator with square minus identity has the same matrix equation. -/
theorem pel_square_matrix {W : Type*} [AddCommGroup W] [Module ℝ W]
    (b : Module.Basis ι ℝ W) (I : Module.End ℝ W) (hI : ∀ x, I (I x) = -x) :
    LinearMap.toMatrix b b I * LinearMap.toMatrix b b I = -1 := by
  rw [← LinearMap.toMatrix_mul]
  have h : I * I = -1 := LinearMap.ext hI
  rw [h, map_neg, LinearMap.toMatrix_one]

/-- Invariance of a bilinear form becomes the transpose matrix equation. -/
theorem pel_isometry_matrix {W : Type*} [AddCommGroup W] [Module ℝ W]
    (b : Module.Basis ι ℝ W) (E : LinearMap.BilinForm ℝ W) (I : Module.End ℝ W)
    (h : ∀ x y, E (I x) (I y) = E x y) :
    (LinearMap.toMatrix b b I).transpose * LinearMap.toMatrix₂ b b E *
      LinearMap.toMatrix b b I = LinearMap.toMatrix₂ b b E := by
  rw [← LinearMap.toMatrix₂_compl₁₂ b b]
  congr 1
  exact LinearMap.ext₂ h

/-- Strict positivity of a symmetric real bilinear form gives a positive matrix. -/
theorem pel_positive_matrix {W : Type*} [AddCommGroup W] [Module ℝ W]
    (b : Module.Basis ι ℝ W) (S : LinearMap.BilinForm ℝ W)
    (hs : S.IsSymm) (hp : ∀ x, x ≠ 0 → 0 < S x x) :
    (LinearMap.toMatrix₂ b b S).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · change (LinearMap.toMatrix₂ b b S).conjTranspose = _
    ext i j
    simpa [Matrix.conjTranspose_apply, LinearMap.toMatrix₂_apply] using hs.eq (b j) (b i)
  · intro x hx
    have hn : b.equivFun.symm x ≠ 0 := by
      intro h
      apply hx
      exact (b.equivFun.apply_symm_apply x).symm.trans (by rw [h, map_zero])
    have hh := hp (b.equivFun.symm x) hn
    have hr : ∀ i, b.repr (b.equivFun.symm x) i = x i :=
      fun i => congrFun (b.equivFun.apply_symm_apply x) i
    rw [← Matrix.toLinearMap₂_toMatrix₂ b b S, Matrix.toLinearMap₂_apply] at hh
    simpa only [hr, smul_eq_mul, star_trivial, dotProduct, Matrix.mulVec,
      Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc] using hh

/-- An invariant alternating form composed with a complex structure is symmetric. -/
theorem pel_twisted_form_symmetric {W : Type*} [AddCommGroup W] [Module ℝ W]
    (E : LinearMap.BilinForm ℝ W) (I : Module.End ℝ W)
    (ha : ∀ x y, E x y = -E y x) (hI : ∀ x, I (I x) = -x)
    (hi : ∀ x y, E (I x) (I y) = E x y) :
    LinearMap.BilinForm.IsSymm (E.compl₂ I) := by
  apply LinearMap.BilinForm.isSymm_def.mpr
  intro x y
  change E x (I y) = E y (I x)
  rw [← hi x (I y), hI, map_neg, ha (I x) y, neg_neg]

#print axioms pel_form_matrix_real
#print axioms pel_square_matrix
#print axioms pel_isometry_matrix
#print axioms pel_positive_matrix
#print axioms pel_twisted_form_symmetric
end HodgeLean.Foundations.Program.GeneralTypeIII
