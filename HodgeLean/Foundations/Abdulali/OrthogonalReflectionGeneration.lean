import HodgeLean.Foundations.Abdulali.OrthogonalReflectionReduction

noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations Matrix
namespace HodgeLean.Foundations.Abdulali

/-- Nonisotropic reflections generate every invertible standard bilinear
isometry, including the zero-dimensional group. -/
theorem orthogonal_reflections_generate (n : ℕ) :
    ∀ (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ)),
      (∀ (w : Fin n → ℂ) (hw : w ⬝ᵥ w ≠ 0), orthogonalReflectionGL w hw ∈ H) →
      ∀ g : Matrix.GeneralLinearGroup (Fin n) ℂ,
        (g : Matrix (Fin n) (Fin n) ℂ).transpose * g = 1 → g ∈ H := by
  induction n with
  | zero =>
    intro H hH g hg
    have he : g = 1 := by
      apply Units.ext
      ext i
      exact Fin.elim0 i
    rw [he]
    exact H.one_mem
  | succ n ih =>
    intro H hH g hg
    let e : Fin (n+1) → ℂ := Pi.single 0 1
    let x := (g : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) *ᵥ e
    have hx : x ⬝ᵥ x = 1 := by
      have h := congrArg (fun A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ => A 0 0) hg
      simpa [x, e, Matrix.mulVec_single_one, dotProduct, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.one_apply] using h
    obtain ⟨a, haH, haO, hax⟩ := orthogonal_unit_vector_reflection_reduction H hH x hx
    have ha : (a : Matrix (Fin (n+1)) (Fin (n+1)) ℂ).transpose * a = 1 := by
      change (a : Matrix (Fin (n+1)) (Fin (n+1)) ℂ).transpose * 1 * a = 1 at haO
      simpa only [mul_one] using haO
    let M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := ↑(a*g)
    have hM : M.transpose * M = 1 := by
      change ((a : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) * (g : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)).transpose * ((a : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) * (g : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) = 1
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc ((a : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)).transpose,
        ha, one_mul, hg]
    have hc : M *ᵥ (Pi.single 0 1) = Pi.single 0 1 := by
      change ((a : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) * (g : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) *ᵥ e = e
      rw [← Matrix.mulVec_mulVec]
      exact hax
    obtain ⟨hMeq, hN⟩ := orthogonal_matrix_tail M hM hc
    let N := M.submatrix Fin.succ Fin.succ
    let w : Matrix.GeneralLinearGroup (Fin n) ℂ :=
      ⟨N, N.transpose, mul_eq_one_comm.mp hN, hN⟩
    let Htail := H.comap (orthogonalTailGL n)
    have htail : ∀ (v : Fin n → ℂ) (hv : v ⬝ᵥ v ≠ 0),
        orthogonalReflectionGL v hv ∈ Htail := by
      intro v hv
      have hv' : (Fin.cons 0 v) ⬝ᵥ (Fin.cons 0 v) ≠ 0 := by
        simpa [dotProduct, Fin.sum_univ_succ] using hv
      have he : orthogonalTailGL n (orthogonalReflectionGL v hv) =
          orthogonalReflectionGL (Fin.cons 0 v) hv' := by
        apply Units.ext
        exact orthogonalTailMatrix_reflection v
      change orthogonalTailGL n (orthogonalReflectionGL v hv) ∈ H
      rw [he]
      exact hH _ hv'
    have hwH := ih Htail htail w hN
    change orthogonalTailGL n w ∈ H at hwH
    have he : orthogonalTailGL n w = a*g := by
      apply Units.ext
      exact hMeq.symm
    rw [he] at hwH
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using H.mul_mem (H.inv_mem haH) hwH

end HodgeLean.Foundations.Abdulali
