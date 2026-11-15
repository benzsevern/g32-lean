import HodgeLean.Foundations.Abdulali.MatrixModule
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.TensorProduct.Map

noncomputable section
open scoped TensorProduct

namespace HodgeLean.Foundations.Abdulali

/-- An alternating form compatible with the symplectic involution of the
matrix algebra factors as the standard alternating form times a symmetric
nondegenerate multiplicity form. This fixes the involution used by the later
orthogonal-centralizer calculation; it asserts no invariant generation.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.1–3.2, pp. 920–921,
and §4, pp. 922–923 (split quaternionic skewhermitian form).
Evaluation on the two standard basis vectors determines the multiplicity form. -/
theorem polarized_multiplicity_aux (n : ℕ)
    (E : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) ⊗[ℂ] (Fin n → ℂ)))
    (halt : ∀ z, E z z = 0) (hnd : E.Nondegenerate)
    (hadj : ∀ (m : Matrix (Fin 2) (Fin 2) ℂ)
      (z w : (Fin 2 → ℂ) ⊗[ℂ] (Fin n → ℂ)),
      E ((Matrix.toLin' m).rTensor (Fin n → ℂ) z) w =
        E z ((Matrix.toLin' m.adjugate).rTensor (Fin n → ℂ) w)) :
    ∃ B : LinearMap.BilinForm ℂ (Fin n → ℂ),
      B.IsSymm ∧ B.Nondegenerate ∧
        ∀ (x y : Fin 2 → ℂ) (u v : Fin n → ℂ),
          E (x ⊗ₜ[ℂ] u) (y ⊗ₜ[ℂ] v) =
            (x 0 * y 1 - x 1 * y 0) * B u v := by
  let a : Fin 2 → ℂ := ![1, 0]
  let b : Fin 2 → ℂ := ![0, 1]
  let t (x : Fin 2 → ℂ) := TensorProduct.mk ℂ (Fin 2 → ℂ) (Fin n → ℂ) x
  let B : LinearMap.BilinForm ℂ (Fin n → ℂ) := E.compl₁₂ (t a) (t b)
  have hvec (m : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin 2 → ℂ)
      (h0 : m 0 0 * x 0 + m 0 1 * x 1 = y 0)
      (h1 : m 1 0 * x 0 + m 1 1 * x 1 = y 1) : Matrix.mulVec m x = y := by
    ext i
    fin_cases i
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h1
  have h00 (u v : Fin n → ℂ) : E (a ⊗ₜ[ℂ] u) (a ⊗ₜ[ℂ] v) = 0 := by
    have h := hadj !![1, 0; 0, 0] (a ⊗ₜ[ℂ] u) (a ⊗ₜ[ℂ] v)
    have hp := hvec !![1, 0; 0, 0] a a (by simp [a]) (by simp [a])
    have hp' := hvec (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ).adjugate a 0
      (by simp [a, Matrix.adjugate_fin_two]) (by simp [a, Matrix.adjugate_fin_two])
    simpa only [LinearMap.rTensor_tmul, Matrix.toLin'_apply, hp, hp',
      TensorProduct.zero_tmul, map_zero] using h
  have h11 (u v : Fin n → ℂ) : E (b ⊗ₜ[ℂ] u) (b ⊗ₜ[ℂ] v) = 0 := by
    have h := hadj !![0, 0; 0, 1] (b ⊗ₜ[ℂ] u) (b ⊗ₜ[ℂ] v)
    have hp := hvec !![0, 0; 0, 1] b b (by simp [b]) (by simp [b])
    have hp' := hvec (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).adjugate b 0
      (by simp [b, Matrix.adjugate_fin_two]) (by simp [b, Matrix.adjugate_fin_two])
    simpa only [LinearMap.rTensor_tmul, Matrix.toLin'_apply, hp, hp',
      TensorProduct.zero_tmul, map_zero] using h
  have h10 (u v : Fin n → ℂ) : E (b ⊗ₜ[ℂ] u) (a ⊗ₜ[ℂ] v) = - B u v := by
    have h := hadj !![0, 0; 1, 0] (a ⊗ₜ[ℂ] u) (a ⊗ₜ[ℂ] v)
    have hp := hvec !![0, 0; 1, 0] a b (by simp [a, b]) (by simp [a, b])
    have hp' := hvec (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ).adjugate a (-b)
      (by simp [a, b, Matrix.adjugate_fin_two]) (by simp [a, b, Matrix.adjugate_fin_two])
    simpa only [LinearMap.rTensor_tmul, Matrix.toLin'_apply, hp, hp',
      TensorProduct.neg_tmul, map_neg, B, t, LinearMap.compl₁₂_apply,
      TensorProduct.mk_apply] using h
  have hsym : B.IsSymm := by
    constructor
    intro u v
    have h := (show E.IsAlt from halt).neg_eq (a ⊗ₜ[ℂ] v) (b ⊗ₜ[ℂ] u)
    rw [h10] at h
    exact neg_injective h.symm
  have hform (x y : Fin 2 → ℂ) (u v : Fin n → ℂ) :
      E (x ⊗ₜ[ℂ] u) (y ⊗ₜ[ℂ] v) =
        (x 0 * y 1 - x 1 * y 0) * B u v := by
    have hx : x = x 0 • a + x 1 • b := by ext i; fin_cases i <;> simp [a, b]
    have hy : y = y 0 • a + y 1 • b := by ext i; fin_cases i <;> simp [a, b]
    conv_lhs => rw [hx, hy]
    simp only [TensorProduct.add_tmul, ← TensorProduct.smul_tmul',
      map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      h00, h11, h10, smul_eq_mul]
    dsimp only [B, t, LinearMap.compl₁₂_apply, TensorProduct.mk_apply]
    change _ = (x 0 * y 1 - x 1 * y 0) * E (a ⊗ₜ[ℂ] u) (b ⊗ₜ[ℂ] v)
    ring
  have hleft : B.SeparatingLeft := by
    intro u hu
    have hz : a ⊗ₜ[ℂ] u = 0 := by
      apply hnd.1
      intro w
      induction w using TensorProduct.inductionOn with
      | tmul y v => rw [hform, hu]; simp
      | add z w hz hw => simp only [map_add, hz, hw, add_zero]
    let q := TensorProduct.comm ℂ (Fin 2 → ℂ) (Fin n → ℂ) ≪≫ₗ
      TensorProduct.piScalarRight ℂ ℂ (Fin n → ℂ) (Fin 2)
    have h := congrArg (fun z => q z 0) hz
    simpa [q, a, TensorProduct.piScalarRight, TensorProduct.piScalarRightHom,
      TensorProduct.piScalarRightHomBil] using h
  refine ⟨B, hsym, ⟨hleft, ?_⟩, hform⟩
  intro v hv
  apply hleft v
  intro u
  rw [hsym.eq]
  exact hv u


end HodgeLean.Foundations.Abdulali
