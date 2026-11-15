import HodgeLean.Foundations.TubularEuler.HermitianProjectorAffine
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Coordinate permutations of the homogeneous projector

Permuting the homogeneous basis permutes both matrix indices.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.TubularEuler

def projectorMatrixPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Fin n → Fin n → ℂ) ≃L[ℝ] (Fin n → Fin n → ℂ) :=
  (show (Fin n → Fin n → ℂ) ≃ₗ[ℝ] (Fin n → Fin n → ℂ) from
    { toFun := fun P i j => P (σ i) (σ j)
      invFun := fun P i j => P (σ.symm i) (σ.symm j)
      left_inv := by intro P; ext i j; simp only [Equiv.apply_symm_apply]
      right_inv := by intro P; ext i j; simp only [Equiv.symm_apply_apply]
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }).toContinuousLinearEquiv

theorem projectorMatrixPermutation_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (P : Fin n → Fin n → ℂ) (i j : Fin n) :
    projectorMatrixPermutation σ P i j = P (σ i) (σ j) := rfl

theorem hermitianProjector_permutation {n : ℕ} (σ : Equiv.Perm (Fin n))
    (v : Fin n → ℂ) :
    hermitianProjector (fun i => v (σ i)) = projectorMatrixPermutation σ (hermitianProjector v) := by
  have hlen : projectorLength (fun i => v (σ i)) = projectorLength v := by
    exact Equiv.sum_comp σ (fun i => Complex.normSq (v i))
  ext i j
  change v (σ i) * star (v (σ j)) / (projectorLength (fun k => v (σ k)) : ℂ) =
    v (σ i) * star (v (σ j)) / (projectorLength v : ℂ)
  rw [hlen]

end HodgeLean.Foundations.TubularEuler
