import HodgeLean.Foundations.Program.RigidStartingSystemDefs
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

def b65r_traceDual (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
    Module.Dual ℂ (Matrix (Fin n) (Fin n) ℂ) where
  toFun A := {
    toFun B := trace (A*B)
    map_add' B C := by rw [mul_add, trace_add]
    map_smul' c B := by rw [mul_smul_comm, trace_smul]; rfl }
  map_add' A B := by
    ext C
    change trace ((A+B)*C) = trace (A*C)+trace (B*C)
    rw [add_mul, trace_add]
  map_smul' c A := by
    ext B
    change trace ((c • A)*B) = c • trace (A*B)
    rw [smul_mul_assoc, trace_smul]

theorem b65r_traceDual_injective (n : ℕ) : Function.Injective (b65r_traceDual n) := by
  intro A B h
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  exact congrArg (fun f : Module.Dual ℂ (Matrix (Fin n) (Fin n) ℂ) ↦ f X) h

def b65r_traceDualEquiv (n : ℕ) : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ]
    Module.Dual ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  LinearEquiv.ofBijective (b65r_traceDual n)
    ⟨b65r_traceDual_injective n,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by simp only [Subspace.dual_finrank_eq])).mp (b65r_traceDual_injective n)⟩

end HodgeLean.Foundations.Program
