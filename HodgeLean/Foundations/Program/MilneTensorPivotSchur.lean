import HodgeLean.Foundations.Program.MilneTensorSchur
import Mathlib.LinearAlgebra.Matrix.Notation

noncomputable section
namespace HodgeLean.Foundations.Program
variable {R : Type*} [CommRing R]

def m1b_scalarPivotUnit (a : Rˣ) : (Matrix Unit Unit R)ˣ :=
  Units.map (Matrix.scalar Unit).toMonoidHom a

theorem m1b_scalar_schur_entries {n : Type*} (a : Rˣ) (b : n → R)
    (D : Matrix n n R) (i j : n) :
    (D - Matrix.of (fun i (_ : Unit) => b i) * (m1b_scalarPivotUnit a).inv *
      Matrix.of (fun (_ : Unit) j => b j)) i j = D i j - a.inv * b i * b j := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_unique, Matrix.of_apply]
  change D i j - b i * a.inv * b j = D i j - a.inv * b i * b j
  ring

def m1b_pairPivotUnit (a : Rˣ) : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := !![0, a.val; -a.val, 0]
  inv := !![0, -a.inv; a.inv, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem m1b_pair_schur_entries {n : Type*} (a : Rˣ) (B : Matrix (Fin 2) n R)
    (D : Matrix n n R) (i j : n) :
    (D + B.transpose * (m1b_pairPivotUnit a).inv * B) i j =
      D i j + a.inv * (B 1 i * B 0 j - B 0 i * B 1 j) := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, m1b_pairPivotUnit, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, mul_neg, zero_add, add_zero]
  ring

end HodgeLean.Foundations.Program
