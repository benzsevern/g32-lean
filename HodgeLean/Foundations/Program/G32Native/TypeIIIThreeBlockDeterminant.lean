import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program.G32Native

/-- The projected skew-Hermitian block on the `K`-basis `(e, je)`.
Source: G32 v0.16, Lemma 8.1, displayed matrix in the proof. -/
def typeIIIProjectedBlock (b l1 l2 l3 : ℚ) :
    Matrix (Fin 2) (Fin 2) (QuadraticAlgebra ℚ (-3) 0) :=
  !![⟨0, l1⟩, ⟨-b * l2, -b * l3⟩; ⟨b * l2, -b * l3⟩, ⟨0, b * l1⟩]

/-- The two-by-two determinant in the commutative Eisenstein algebra.
Source: G32 v0.16, Lemma 8.1; compare `HodgeBlocks.TypeIII.det_hEntries`. -/
theorem typeIIIProjectedBlock_det (b l1 l2 l3 : ℚ) :
    (typeIIIProjectedBlock b l1 l2 l3).det =
      algebraMap ℚ (QuadraticAlgebra ℚ (-3) 0)
        (b * (-3 * l1 ^ 2 + b * l2 ^ 2 + 3 * b * l3 ^ 2)) := by
  rw [Matrix.det_fin_two]
  ext <;> simp [typeIIIProjectedBlock, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul, pow_two, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.re_ofNat,
    QuadraticAlgebra.im_ofNat] <;> ring

/-- The actual six-by-six block-diagonal determinant, with all three blocks.
Source: G32 v0.16, Lemma 8.1, equation `det T_K = b³ disc(T)`. -/
theorem typeIIIThreeBlock_det (b : ℚ) (l1 l2 l3 : Fin 3 → ℚ) :
    (Matrix.blockDiagonal (fun i => typeIIIProjectedBlock b (l1 i) (l2 i) (l3 i))).det =
      algebraMap ℚ (QuadraticAlgebra ℚ (-3) 0)
        (b ^ 3 * ∏ i, (-3 * l1 i ^ 2 + b * l2 i ^ 2 + 3 * b * l3 i ^ 2)) := by
  rw [Matrix.det_blockDiagonal]
  simp only [typeIIIProjectedBlock_det, ← map_prod]
  congr 1
  rw [Finset.prod_mul_distrib]
  simp

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIProjectedBlock_det
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIThreeBlock_det
