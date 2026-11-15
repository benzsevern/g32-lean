import HodgeLean.Foundations.Abdulali.QuaternionSplit
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi

noncomputable section
open scoped TensorProduct

namespace HodgeLean.Foundations.Abdulali

private def matrixMultiplicity (V : Type*) [AddCommGroup V] [Module ℂ V]
    (ρ : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Module.End ℂ V) : Submodule ℂ V :=
  LinearMap.range (ρ (Matrix.single 0 0 1))

private lemma action_mul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Module.End ℂ V)
    (a b : Matrix (Fin 2) (Fin 2) ℂ) (v : V) :
    ρ a (ρ b v) = ρ (a * b) v := by
  rw [map_mul, Module.End.mul_apply]

private def matrixMultiplicityEquiv (V : Type*) [AddCommGroup V] [Module ℂ V]
    (ρ : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Module.End ℂ V) :
    V ≃ₗ[ℂ] (Fin 2 → matrixMultiplicity V ρ) where
  toFun v i := ⟨ρ (Matrix.single 0 i 1) v,
    ρ (Matrix.single 0 i 1) v, by simp [action_mul]⟩
  invFun w := ∑ i, ρ (Matrix.single i 0 1) (w i).val
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp
  left_inv v := by
    simp only [action_mul, Matrix.single_mul_single_same, one_mul]
    rw [← LinearMap.sum_apply, ← map_sum]
    simp [Matrix.sum_single_one]
  right_inv w := by
    ext i
    simp only [map_sum, action_mul]
    rw [Finset.sum_eq_single i]
    · obtain ⟨v, hv⟩ := (w i).property
      rw [Matrix.single_mul_single_same, one_mul, ← hv, action_mul]
      simp
    · intro j _ hji
      simp [Matrix.single_mul_single_of_ne _ _ _ _ hji.symm]
    · simp

/-- A finite-dimensional unital module over the split quaternion algebra is a
sum of standard two-dimensional modules. The equation retains the action under
the chosen equivalence, including the multiplicity space of dimension zero.
Source: Abdulali, Annals of Mathematics 155 (2002), §4, p. 923,
the decomposition into two copies of the standard orthogonal representation;
the matrix-module step here is the underlying elementary Morita decomposition.
The multiplicity space is the range of the first diagonal matrix unit. -/
theorem matrix_module_aux (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (ρ : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] Module.End ℂ V) :
    ∃ (n : ℕ) (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin n → ℂ)) ≃ₗ[ℂ] V),
      ∀ (m : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (u : Fin n → ℂ),
        ρ m (e (x ⊗ₜ[ℂ] u)) = e ((Matrix.mulVec m x) ⊗ₜ[ℂ] u) := by
  let W := matrixMultiplicity V ρ
  let d := matrixMultiplicityEquiv V ρ
  let n := Module.finrank ℂ W
  let f : (Fin n → ℂ) ≃ₗ[ℂ] W := (Module.finBasis ℂ W).equivFun.symm
  let q : ((Fin 2 → ℂ) ⊗[ℂ] (Fin n → ℂ)) ≃ₗ[ℂ] (Fin 2 → W) :=
    (TensorProduct.congr (LinearEquiv.refl ℂ _) f) ≪≫ₗ
      TensorProduct.comm ℂ _ _ ≪≫ₗ TensorProduct.piScalarRight ℂ ℂ W (Fin 2)
  have hq (x : Fin 2 → ℂ) (u : Fin n → ℂ) (i : Fin 2) :
      q (x ⊗ₜ[ℂ] u) i = x i • f u := by
    simp [q, TensorProduct.piScalarRight, TensorProduct.piScalarRightHom,
      TensorProduct.piScalarRightHomBil]
  refine ⟨n, q ≪≫ₗ d.symm, ?_⟩
  intro m x u
  apply d.injective
  change d (ρ m (d.symm (q (x ⊗ₜ[ℂ] u)))) =
    d (d.symm (q ((Matrix.mulVec m x) ⊗ₜ[ℂ] u)))
  rw [d.apply_symm_apply]
  ext i
  have hm : (Matrix.single 0 i (1 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * m =
      ∑ j : Fin 2, m i j • Matrix.single 0 j 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> fin_cases i <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single]
  change ρ (Matrix.single 0 i 1) (ρ m (d.symm (q (x ⊗ₜ[ℂ] u)))) = _
  rw [action_mul, hm]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  have hd (j : Fin 2) : ρ (Matrix.single 0 j 1) (d.symm (q (x ⊗ₜ[ℂ] u))) =
      ((q (x ⊗ₜ[ℂ] u)) j).val := by
    exact congrArg (fun w => (w j).val) (d.apply_symm_apply (q (x ⊗ₜ[ℂ] u)))
  simp only [hd, hq, SetLike.val_smul, smul_smul]
  simp [Matrix.mulVec, dotProduct, add_smul]


end HodgeLean.Foundations.Abdulali
