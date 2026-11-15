import HodgeLean.Foundations.Abdulali.RationalMatrixCurve
import HodgeLean.Foundations.Abdulali.ReflectionPair

noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations Matrix
namespace HodgeLean.Foundations.Abdulali

/-- A polynomial family of nonisotropic vectors connects the corresponding
reflection pairs inside the identity component of the actual SO group. -/
theorem polynomial_reflection_pair_mem_component {n : ℕ}
    (z : Fin n → Polynomial ℂ) (s t : ℂ)
    (hs : (fun i => (z i).eval s) ⬝ᵥ (fun i => (z i).eval s) ≠ 0)
    (ht : (fun i => (z i).eval t) ⬝ᵥ (fun i => (z i).eval t) ≠ 0) :
    orthogonalReflectionGL (fun i => (z i).eval t) ht *
      orthogonalReflectionGL (fun i => (z i).eval s) hs ∈
        g1_identityComponent (specialOrthogonalMatrixGroup (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  classical
  let q : Polynomial ℂ := ∑ i, z i * z i
  have hq (a : ℂ) : q.eval a = (fun i => (z i).eval a) ⬝ᵥ (fun i => (z i).eval a) := by
    simp only [q, Polynomial.eval_finsetSum, Polynomial.eval_mul, dotProduct]
  have hq0 : q ≠ 0 := by
    intro he
    exact hs (by rw [← hq s, he, Polynomial.eval_zero])
  let D := {a : ℂ // q.eval a ≠ 0}
  have hi : Set.Infinite {a : ℂ | q.eval a ≠ 0} := by
    have hf := Polynomial.finite_setOfPred_isRoot hq0
    exact hf.infinite_compl
  letI : Infinite D := hi.to_subtype
  let a₀ : D := ⟨s, by rw [hq]; exact hs⟩
  let a₁ : D := ⟨t, by rw [hq]; exact ht⟩
  have hz (a : D) : (fun i => (z i).eval a.val) ⬝ᵥ
      (fun i => (z i).eval a.val) ≠ 0 := by rw [← hq]; exact a.property
  let c (a : D) := orthogonalReflectionGL (fun i => (z i).eval a.val) (hz a) *
    orthogonalReflectionGL (fun i => (z i).eval s) hs
  let R := orthogonalReflectionMatrix (fun i => (z i).eval s)
  let p : Fin n × Fin n → Polynomial ℂ := fun ij =>
    ∑ k, (q * Polynomial.C ((1 : Matrix (Fin n) (Fin n) ℂ) ij.1 k) -
      Polynomial.C 2 * z ij.1 * z k) * Polynomial.C (R k ij.2)
  have hp (a : D) (ij : Fin n × Fin n) :
      g1_coords (c a) ij = (p ij).eval a.val / q.eval a.val := by
    change (orthogonalReflectionMatrix (fun i => (z i).eval a.val) * R) ij.1 ij.2 = _
    rw [Matrix.mul_apply]
    have hr (i k : Fin n) : orthogonalReflectionMatrix
        (fun i => (z i).eval a.val) i k =
        (q.eval a.val * (1 : Matrix (Fin n) (Fin n) ℂ) i k -
          2 * (z i).eval a.val * (z k).eval a.val) / q.eval a.val := by
      simp only [orthogonalReflectionMatrix, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul, vecMulVec_apply, ← hq]
      field_simp [a.property]
    simp_rw [hr, div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    congr 1
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_C]
  have hc₀ : c a₀ = 1 := by
    apply Units.ext
    change orthogonalReflectionMatrix (fun i => (z i).eval s) *
      orthogonalReflectionMatrix (fun i => (z i).eval s) = 1
    exact orthogonalReflectionMatrix_sq _ hs
  exact rational_matrix_curve_mem_component _ (fun a : D => a.val)
    Subtype.val_injective q (fun a => a.property) c p hp
    (fun a => reflection_pair_mem_specialOrthogonal _ _ (hz a) hs) a₀ a₁ hc₀

/-- Every pair of nonisotropic standard reflections lies in the identity
component, using the affine line of reflecting vectors with its poles removed. -/
theorem reflection_pair_mem_component {n : ℕ} (u v : Fin n → ℂ)
    (hu : u ⬝ᵥ u ≠ 0) (hv : v ⬝ᵥ v ≠ 0) :
    orthogonalReflectionGL u hu * orthogonalReflectionGL v hv ∈
      g1_identityComponent (specialOrthogonalMatrixGroup (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  let z : Fin n → Polynomial ℂ := fun i => Polynomial.C (v i) +
    Polynomial.X * Polynomial.C (u i - v i)
  have h0 : (fun i => (z i).eval 0) = v := by
    funext i
    simp only [z, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, zero_mul, add_zero]
  have h1 : (fun i => (z i).eval 1) = u := by
    funext i
    simp only [z, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, one_mul, add_sub_cancel]
  have hs : (fun i => (z i).eval 0) ⬝ᵥ (fun i => (z i).eval 0) ≠ 0 := by rw [h0]; exact hv
  have ht : (fun i => (z i).eval 1) ⬝ᵥ (fun i => (z i).eval 1) ≠ 0 := by rw [h1]; exact hu
  have h := polynomial_reflection_pair_mem_component z 0 1 hs ht
  simpa only [h0, h1] using h

end HodgeLean.Foundations.Abdulali
