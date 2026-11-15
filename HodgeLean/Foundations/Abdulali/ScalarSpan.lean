import Mathlib.Algebra.Algebra.Rat
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Abdulali

/-- Extending a full rational subspace contains every complexified vector.
Source: scalar extension of vector spaces. -/
theorem mem_complex_span_of_eq_top {V : Type*} [AddCommGroup V] [Module ℚ V]
    (P : Submodule ℚ V) (h : P = ⊤) (v : ℂ ⊗[ℚ] V) : v ∈ P.baseChange ℂ := by
  subst P
  rw [Submodule.baseChange_top]
  exact Submodule.mem_top

end HodgeLean.Foundations.Abdulali
