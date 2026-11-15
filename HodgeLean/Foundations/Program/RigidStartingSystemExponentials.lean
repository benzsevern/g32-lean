import HodgeLean.Foundations.Program.RigidStartingSystemNonresonance
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

def b65r_operatorEquiv (n : ℕ) : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ]
    ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :=
  Matrix.toLinAlgEquiv'.trans (Module.End.toContinuousLinearMap (Fin n → ℂ))

theorem b65r_operatorEquiv_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    b65r_operatorEquiv n A = b65r_operator A := rfl

theorem b65r_exp_diagonal {n : ℕ} (d : Fin n → ℂ) :
    NormedSpace.exp (b65r_operator (diagonal d)) =
      b65r_operator (diagonal (fun i ↦ NormedSpace.exp (d i))) := by
  let f : (Fin n → ℂ) →ₐ[ℂ] ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :=
    (b65r_operatorEquiv n).toAlgHom.comp (diagonalAlgHom (n := Fin n) (α := ℂ) ℂ)
  have hf : Continuous f := f.toLinearMap.continuous_of_finiteDimensional
  have h := NormedSpace.map_exp f hf d
  simpa only [f, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, diagonalAlgHom_apply,
    b65r_operatorEquiv_apply, Pi.exp_def] using h.symm

theorem b65r_conjugate_of_eigenbases {n : ℕ}
    (R G : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (P Q : ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ))ˣ)
    (d e : Fin n → ℂ) (c : ℂ)
    (hR : R*P = P*b65r_operator (diagonal d))
    (hG : G*Q = Q*b65r_operator (diagonal e))
    (hexp : ∀ j, NormedSpace.exp (c*d j) = e j) :
    ∃ C : ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ))ˣ,
      (C : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))*NormedSpace.exp (c • R)*↑(C⁻¹) = G := by
  let : NormedAlgebra ℚ ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hr : R = ↑P*b65r_operator (diagonal d)*↑(P⁻¹) := by
    calc
      R = (R*↑P)*↑(P⁻¹) := by simp [mul_assoc]
      _ = _ := by rw [hR]
  have hg : G = ↑Q*b65r_operator (diagonal e)*↑(Q⁻¹) := by
    calc
      G = (G*↑Q)*↑(Q⁻¹) := by simp [mul_assoc]
      _ = _ := by rw [hG]
  have he : NormedSpace.exp (c • b65r_operator (diagonal d)) =
      b65r_operator (diagonal e) := by
    rw [← b65r_operator_smul, ← diagonal_smul, b65r_exp_diagonal]
    congr 2
    funext j
    exact hexp j
  have hc : c • R = ↑P*(c • b65r_operator (diagonal d))*↑(P⁻¹) := by
    rw [hr]
    simp only [smul_mul_assoc, mul_smul_comm]
  refine ⟨Q*P⁻¹, ?_⟩
  rw [hc, NormedSpace.exp_units_conj, he, hg]
  simp [mul_assoc]

end HodgeLean.Foundations.Program
