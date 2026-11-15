import HodgeLean.Foundations.Abdulali.PolarizedMultiplicity

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Abdulali

/-- A quaternion splitting retaining conjugation and the chosen quadratic
subfield generator. Conjugation corresponds to the symplectic adjugate,
not entrywise complex conjugation. The two eigenspaces of the selected
generator have eigenvalues `s` and `-s` in these fixed coordinates.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.1–3.2 and §4.
The explicit matrices refine the algebra splitting of `quaternion_split_aux`. -/
theorem quaternion_split_with_involution (b : ℂ) (hb : b ≠ 0) :
    ∃ (s : ℂ), s ^ 2 = -3 ∧
      ∃ e : ℍ[ℂ, -3, 0, b] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ,
        (∀ q, e (star q) = (e q).adjugate) ∧
        e ⟨0, 1, 0, 0⟩ = !![s, 0; 0, -s] := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-3 : ℂ) (by norm_num : 0 < 2)
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  refine ⟨s, hs, {
    toFun := fun q => !![q.re + s * q.imI, b * (q.imJ + s * q.imK);
      q.imJ - s * q.imK, q.re - s * q.imI]
    invFun := fun m => ⟨(m 0 0 + m 1 1) / 2, (m 0 0 - m 1 1) / (2 * s),
      (m 1 0 + m 0 1 / b) / 2, (m 0 1 / b - m 1 0) / (2 * s)⟩
    left_inv := ?_
    right_inv := ?_
    map_mul' := ?_
    map_add' := ?_
    commutes' := ?_ }, ?_, ?_⟩
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
  · intro q
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.adjugate_fin_two] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp

end HodgeLean.Foundations.Abdulali
