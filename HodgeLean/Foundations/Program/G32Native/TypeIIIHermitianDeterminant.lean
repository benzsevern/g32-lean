import HodgeLean.Foundations.Program.G32Native.TypeIIIThreeBlockDeterminant
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

noncomputable section
namespace HodgeLean.Foundations.Program.G32Native

/-- The matrix obtained from the projected trace matrix by the manuscript's
Hermitian conversion. -/
def typeIIIHermitianMatrix (b : ℚ) (l1 l2 l3 : Fin 3 → ℚ) :
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) (QuadraticAlgebra ℚ (-3) 0) :=
  (⟨0, 2⟩ : QuadraticAlgebra ℚ (-3) 0) •
    (Matrix.blockDiagonal (fun i => typeIIIProjectedBlock b (l1 i) (l2 i) (l3 i))).map
      (starRingEnd _)

/-- The Hermitian conversion contributes the factor `(2u)^6 = -1728`.
This calculation retains the sign and all six indices. -/
theorem typeIIIHermitianMatrix_det (b : ℚ) (l1 l2 l3 : Fin 3 → ℚ) :
    (typeIIIHermitianMatrix b l1 l2 l3).det =
      algebraMap ℚ (QuadraticAlgebra ℚ (-3) 0)
        (-1728 * b ^ 3 * ∏ i, (-3 * l1 i ^ 2 + b * l2 i ^ 2 + 3 * b * l3 i ^ 2)) := by
  rw [typeIIIHermitianMatrix, Matrix.det_smul]
  have hm := (starRingEnd (QuadraticAlgebra ℚ (-3) 0)).map_det
    (Matrix.blockDiagonal (fun i => typeIIIProjectedBlock b (l1 i) (l2 i) (l3 i)))
  change _ = (Matrix.map _ (starRingEnd _)).det at hm
  rw [← hm, typeIIIThreeBlock_det]
  have hp : (⟨0, 2⟩ : QuadraticAlgebra ℚ (-3) 0) ^ 6 =
      algebraMap ℚ _ (-1728) := by
    ext <;> norm_num [pow_succ, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  simp only [Fintype.card_prod, Fintype.card_fin] 
  rw [show 2 * 3 = 6 from rfl, hp]
  have hs (r : ℚ) : star (algebraMap ℚ (QuadraticAlgebra ℚ (-3) 0) r) =
      algebraMap ℚ _ r := by
    ext <;> simp
  rw [starRingEnd_apply, hs, ← map_mul]
  congr 1
  ring

/-- In even dimension, minus conjugation preserves a rational matrix
 determinant. This is the determinant operation required by contraction. -/
theorem typeIII_det_neg_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (QuadraticAlgebra ℚ (-3) 0)) (r : ℚ)
    (hM : M.det = algebraMap ℚ _ r) (heven : Even (Fintype.card ι)) :
    (-(M.map (starRingEnd _))).det = algebraMap ℚ _ r := by
  rw [Matrix.det_neg, heven.neg_one_pow, one_mul]
  have hm := (starRingEnd (QuadraticAlgebra ℚ (-3) 0)).map_det M
  change _ = (M.map (starRingEnd _)).det at hm
  rw [← hm, hM, starRingEnd_apply]
  ext <;> simp

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIHermitianMatrix_det

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_det_neg_conjugate
