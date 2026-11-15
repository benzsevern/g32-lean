import HodgeLean.Foundations.Abdulali.OrthogonalTailEmbedding
import HodgeLean.Foundations.Abdulali.SpecialOrthogonalLie

noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations Matrix
namespace HodgeLean.Foundations.Abdulali

/-- At most two nonisotropic reflections take a unit vector to the first
coordinate vector. Each reflection is retained in the supplied subgroup. -/
theorem orthogonal_unit_vector_reflection_reduction {n : ℕ}
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin (n+1)) ℂ))
    (hH : ∀ (w : Fin (n+1) → ℂ) (hw : w ⬝ᵥ w ≠ 0), orthogonalReflectionGL w hw ∈ H)
    (x : Fin (n+1) → ℂ) (hx : x ⬝ᵥ x = 1) :
    ∃ a ∈ H, a ∈ (g1_isometryGroup (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)).carrier ∧
      (a : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) *ᵥ x = Pi.single 0 1 := by
  classical
  let e : Fin (n+1) → ℂ := Pi.single 0 1
  have he : e ⬝ᵥ e = 1 := by simp [e, single_dotProduct]
  have he0 : e ⬝ᵥ e ≠ 0 := by rw [he]; exact one_ne_zero
  have hr (w : Fin (n+1) → ℂ) (hw : w ⬝ᵥ w ≠ 0) :
      orthogonalReflectionGL w hw ∈
        (g1_isometryGroup (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)).carrier :=
    orthogonalReflectionMatrix_isometry w hw
  by_cases hd : (x-e) ⬝ᵥ (x-e) = 0
  · have hp : (x+e) ⬝ᵥ (x+e) ≠ 0 := by
      intro hz
      have hh : (x-e) ⬝ᵥ (x-e) + (x+e) ⬝ᵥ (x+e) = 4 := by
        simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add]
        rw [hx, he]
        ring
      rw [hd, hz] at hh
      norm_num at hh
    refine ⟨orthogonalReflectionGL e he0 * orthogonalReflectionGL (x+e) hp,
      H.mul_mem (hH e he0) (hH (x+e) hp),
      (g1_isometryGroup (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)).carrier.mul_mem
        (hr e he0) (hr (x+e) hp), ?_⟩
    change (orthogonalReflectionMatrix e * orthogonalReflectionMatrix (x+e)) *ᵥ x = e
    rw [← Matrix.mulVec_mulVec]
    have hn : x ⬝ᵥ x = (-e) ⬝ᵥ (-e) := by
      rw [neg_dotProduct, dotProduct_neg, neg_neg, hx, he]
    have hm : orthogonalReflectionMatrix (x+e) *ᵥ x = -e := by
      simpa only [sub_neg_eq_add] using orthogonalReflectionMatrix_maps_equal_norm x (-e) hn
        (by simpa only [sub_neg_eq_add] using hp)
    rw [hm, Matrix.mulVec_neg, orthogonalReflectionMatrix_mulVec_self e he0, neg_neg]
  · refine ⟨orthogonalReflectionGL (x-e) hd, hH (x-e) hd, hr (x-e) hd, ?_⟩
    exact orthogonalReflectionMatrix_maps_equal_norm x e (hx.trans he.symm) hd

/-- An orthogonal matrix fixing the first coordinate is the identity on that
coordinate and an orthogonal matrix on its tail. -/
theorem orthogonal_matrix_tail {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hM : M.transpose * M = 1) (hc : M *ᵥ (Pi.single 0 1) = Pi.single 0 1) :
    M = orthogonalTailMatrix (M.submatrix Fin.succ Fin.succ) ∧
      (M.submatrix Fin.succ Fin.succ).transpose * M.submatrix Fin.succ Fin.succ = 1 := by
  classical
  have hcol (i : Fin (n+1)) : M i 0 = (Pi.single 0 (1 : ℂ) : Fin (n+1) → ℂ) i := by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hc i
  have hrow (j : Fin (n+1)) : M 0 j = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) 0 j := by
    have h := congrArg (fun A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ => A 0 j) hM
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hcol] at h
    simpa [Pi.single_apply] using h
  constructor
  · ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [orthogonalTailMatrix, Matrix.submatrix_apply, hrow, hcol, Pi.single_apply, Matrix.one_apply, Fin.succ_ne_zero, eq_comm]
  · ext i j
    have h := congrArg (fun A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ => A i.succ j.succ) hM
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, hrow] at h
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.one_apply, Fin.succ_ne_zero, eq_comm] using h

end HodgeLean.Foundations.Abdulali
