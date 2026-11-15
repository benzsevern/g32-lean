import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section
open scoped Quaternion

namespace HodgeLean.Foundations.Abdulali

/-- Splitting the complexified definite quaternion presentation. The parameter is
nonzero; the rational negative parameter in `GeneralPELMember` has this property.
This is an algebra statement, with no Hodge or algebraicity assertion.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.1–3.2, pp. 920–921
(the splitting of the quaternion algebra over an algebraically closed field).
The generator matrices and their inverse coordinate map are explicit. -/
theorem quaternion_split_aux (b : ℂ) (hb : b ≠ 0) :
    Nonempty (ℍ[ℂ, -3, 0, b] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-3 : ℂ) (by norm_num : 0 < 2)
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  refine ⟨{
    toFun := fun q => !![q.re + s * q.imI, b * (q.imJ + s * q.imK);
      q.imJ - s * q.imK, q.re - s * q.imI]
    invFun := fun m => ⟨(m 0 0 + m 1 1) / 2, (m 0 0 - m 1 1) / (2 * s),
      (m 1 0 + m 0 1 / b) / 2, (m 0 1 / b - m 1 0) / (2 * s)⟩
    left_inv := ?_
    right_inv := ?_
    map_mul' := ?_
    map_add' := ?_
    commutes' := ?_ }⟩
  · intro q
    ext <;> dsimp <;> field_simp <;> ring
  · intro m
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp <;> field_simp <;> ring
  · intro q r
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring_nf <;> simp [hs] <;> ring
  · intro q r
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  · intro c
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [QuaternionAlgebra.algebraMap_eq, Matrix.algebraMap_eq_diagonal]


end HodgeLean.Foundations.Abdulali
