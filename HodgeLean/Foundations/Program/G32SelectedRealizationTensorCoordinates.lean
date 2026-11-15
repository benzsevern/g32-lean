import HodgeLean.Foundations.Program.G32SelectedRealizationEigenGenerator
import Mathlib.LinearAlgebra.TensorProduct.Pi

noncomputable section
open HodgeLean.Foundations
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

def g32y_cyclotomic_tensor_coordinates {V : Type*} [AddCommGroup V] [Module ℚ V]
    {m d : ℕ} (e : V ≃ₗ[ℚ] (Fin d → cyc_Field m)) :
    (ℂ ⊗[ℚ] V) ≃ₗ[ℂ] (Fin d → ℂ ⊗[ℚ] cyc_Field m) :=
  (e.baseChange ℚ ℂ _ _).trans (TensorProduct.piRight ℚ ℂ ℂ (fun _ : Fin d ↦ cyc_Field m))

theorem g32y_tensor_coordinates_scalar {V : Type*} [AddCommGroup V] [Module ℚ V]
    {m d : ℕ} (e : V ≃ₗ[ℚ] (Fin d → cyc_Field m)) (a : cyc_Field m)
    (v : ℂ ⊗[ℚ] V) (i : Fin d) :
    g32y_cyclotomic_tensor_coordinates e ((cyc_scalar e a).baseChange ℂ v) i =
      (Algebra.lmul ℚ (cyc_Field m) a).baseChange ℂ
        (g32y_cyclotomic_tensor_coordinates e v i) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    change c ⊗ₜ[ℚ] (e (e.symm (fun j ↦ a * e v j))) i = c ⊗ₜ[ℚ] (a * e v i)
    rw [e.apply_symm_apply]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]

end HodgeLean.Foundations.Program
