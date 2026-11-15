import HodgeLean.Foundations.MatrixAlgGroupLie

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations MvPolynomial
variable {k : Type*} [Field k] {n : ℕ}
local notation "P" => MvPolynomial (Fin n × Fin n) k
local notation "M" => Matrix (Fin n) (Fin n) k
local notation "MP" => Matrix (Fin n) (Fin n) P

/-- Apply the point differential entry by entry. -/
def pelMatrixDifferential (X : M) (A : MP) : M := A.map (g1_diffAt X)

lemma pelMatrixDifferential_mul (X : M) (A B : MP) :
    pelMatrixDifferential X (A * B) =
      (eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k))).mapMatrix A *
        pelMatrixDifferential X B + pelMatrixDifferential X A *
      (eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k))).mapMatrix B := by
  ext i j
  simp only [pelMatrixDifferential, Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply,
    RingHom.mapMatrix_apply]
  rw [map_sum]
  simp only [g1_diffAt_apply, g1_differential_mul, Finset.sum_add_distrib, Matrix.map_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma pelMatrixDifferential_var (X : M) :
    pelMatrixDifferential X (g1_varMatrix k n) = X := by
  ext i j
  simp [pelMatrixDifferential, g1_varMatrix, g1_diffAt_apply, g1_differential_X]

lemma pelMatrixDifferential_const (X A : M) :
    pelMatrixDifferential X (A.map C) = 0 := by
  ext i j
  simp [pelMatrixDifferential, g1_diffAt_apply, g1_differential_C]

lemma pelMatrixDifferential_adjugate (X : M) :
    pelMatrixDifferential X (g1_varMatrix k n).adjugate =
      g1_differential (g1_varMatrix k n).det X • (1 : M) - X := by
  have he : (eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k))).mapMatrix
      (g1_varMatrix k n).adjugate = (1 : M) := by
    rw [RingHom.map_adjugate, g1_mapMatrix_eval_varMatrix]
    simp
  have h := congrArg (pelMatrixDifferential X) (Matrix.mul_adjugate (g1_varMatrix k n))
  rw [pelMatrixDifferential_mul, pelMatrixDifferential_var, g1_mapMatrix_eval_varMatrix,
    he, Units.val_one, Matrix.one_mul, Matrix.mul_one] at h
  have hr : pelMatrixDifferential X ((g1_varMatrix k n).det • (1 : MP)) =
      g1_differential (g1_varMatrix k n).det X • (1 : M) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [pelMatrixDifferential, Matrix.smul_apply, Matrix.one_apply, g1_diffAt_apply]
    · simp [pelMatrixDifferential, Matrix.smul_apply, Matrix.one_apply, hij]
  rw [hr] at h
  exact eq_sub_of_add_eq h

lemma pelMatrixDifferential_adjugate_conjugation (X Y : M) :
    pelMatrixDifferential X ((g1_varMatrix k n).adjugate * Y.map C * g1_varMatrix k n) =
      g1_differential (g1_varMatrix k n).det X • Y - (X * Y - Y * X) := by
  have hc : (eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k))).mapMatrix
      (Y.map C) = Y := by ext i j; simp
  have ha : (eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k))).mapMatrix
      (g1_varMatrix k n).adjugate = (1 : M) := by
    rw [RingHom.map_adjugate, g1_mapMatrix_eval_varMatrix]; simp
  rw [pelMatrixDifferential_mul, pelMatrixDifferential_mul,
    pelMatrixDifferential_const, pelMatrixDifferential_adjugate,
    pelMatrixDifferential_var, map_mul, ha, hc, g1_mapMatrix_eval_varMatrix, Units.val_one]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, zero_add, sub_mul,
    smul_mul_assoc, Matrix.one_mul]
  abel

/-- Pair a polynomial matrix with the linear functional given by a point differential. -/
def pelTangentPolynomial (f : P) (A : MP) : P :=
  ∑ ij : Fin n × Fin n,
    C (eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) (pderiv ij f)) * A ij.1 ij.2

lemma pel_eval_tangentPolynomial (f : P) (A : MP)
    (g : Matrix.GeneralLinearGroup (Fin n) k) :
    eval (g1_coords g) (pelTangentPolynomial f A) =
      g1_differential f ((eval (g1_coords g)).mapMatrix A) := by
  simp only [pelTangentPolynomial, map_sum, map_mul, eval_C, g1_differential_apply,
    RingHom.mapMatrix_apply, Matrix.map_apply]

lemma pel_differential_tangentPolynomial (f : P) (A : MP) (X : M) :
    g1_differential (pelTangentPolynomial f A) X =
      g1_differential f (pelMatrixDifferential X A) := by
  rw [← g1_diffAt_apply]
  simp only [pelTangentPolynomial, map_sum, g1_diffAt_apply, g1_differential_C_mul]
  simp only [g1_differential_apply, pelMatrixDifferential, Matrix.map_apply, g1_diffAt_apply]

end HodgeLean.Foundations.Program.GeneralTypeIII
