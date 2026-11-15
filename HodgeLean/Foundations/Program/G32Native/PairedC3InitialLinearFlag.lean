import HodgeLean.Foundations.Program.G32Native.PairedC3FullRatioKernel
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-! # The independent equations of the full initial linear flag -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native
variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {s : ℕ}

/-- The retained equations are independent in the full section-space
model, including its holomorphic summand. -/
theorem paired_c3_full_ratio_surjective (t : Fin s → K) :
    Function.Surjective (pairedC3FullRatioEquations (W := W) t) := by
  intro a
  obtain ⟨v, hv⟩ := paired_c3_retained_ratio_surjective t a
  exact ⟨(0, v), hv⟩

/-- The normal coordinate space to the linear kernel has exactly the
retained equation coordinates, through the original quotient map.
Source: Hartshorne, Algebraic Geometry, I.2, linear subspaces. -/
def pairedC3InitialLinearQuotient (t : Fin s → K) :
    ((W × pencilResidueSpace K (s + 1)) ⧸
      LinearMap.ker (pairedC3FullRatioEquations (W := W) t)) ≃ₗ[K] (Fin s → K) :=
  (pairedC3FullRatioEquations (W := W) t).quotKerEquivOfSurjective
    (paired_c3_full_ratio_surjective t)

/-- The quotient identification preserves the actual equations. -/
theorem paired_c3_initial_linear_quotient_mk (t : Fin s → K)
    (v : W × pencilResidueSpace K (s + 1)) :
    pairedC3InitialLinearQuotient (W := W) t (Submodule.Quotient.mk v) =
      pairedC3FullRatioEquations t v :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

/-- Counting the equations uses the full section space, rather than
replacing it with its selected kernel. -/
theorem paired_c3_initial_linear_codimension (t : Fin s → K) :
    Module.finrank K ((W × pencilResidueSpace K (s + 1)) ⧸
      LinearMap.ker (pairedC3FullRatioEquations (W := W) t)) = s := by
  rw [(pairedC3InitialLinearQuotient (W := W) t).finrank_eq,
    Module.finrank_fin_fun]

#print axioms paired_c3_full_ratio_surjective
#print axioms pairedC3InitialLinearQuotient
#print axioms paired_c3_initial_linear_quotient_mk
#print axioms paired_c3_initial_linear_codimension
end HodgeLean.Foundations.Program.G32Native
