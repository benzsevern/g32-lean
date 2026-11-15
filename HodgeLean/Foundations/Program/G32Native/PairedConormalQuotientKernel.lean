import HodgeLean.Foundations.Program.G32Native.PairedConormalKernelDualCoordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The actual relation line of a finite quotient -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

/-- A nonzero relation of a surjective quotient with the specified actual
fibre rank generates its entire kernel. -/
theorem conormal_quotient_kernel_eq_relation_span (k : ℕ)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (π : (ℂ × (Fin k → ℂ)) →ₗ[ℂ] W) (hπ : Function.Surjective π)
    (hdim : Module.finrank ℂ W = k)
    (v : ℂ × (Fin k → ℂ)) (hv : v ≠ 0) (hrel : π v = 0) :
    LinearMap.ker π = Submodule.span ℂ {v} := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · exact (Submodule.span_singleton_le_iff_mem v _).mpr hrel
  · rw [finrank_span_singleton hv]
    have hr := π.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hπ, finrank_top, hdim] at hr
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi,
      Fintype.card_fin, mul_one] at hr
    omega

end HodgeLean.Foundations.Program.G32Native
