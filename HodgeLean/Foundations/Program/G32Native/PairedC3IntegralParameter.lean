import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Properties

/-! # Regular local generators on an integral slice -/
noncomputable section
set_option maxHeartbeats 200000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A local principal equation of a proper support on an integral scheme
is regular on every nonempty affine neighbourhood.
Source: Hartshorne, Algebraic Geometry, II.3 and II.6. -/
theorem paired_c3_integral_parameter_regular
    {X : Scheme} [IsIntegral X] (I : X.IdealSheafData)
    (hproper : I.support ≠ ⊤) (U : X.affineOpens) [Nonempty U.1]
    (v : Γ(X, U)) (hv : I.ideal U = Ideal.span {v}) :
    IsSMulRegular Γ(X, U) v := by
  have hv0 : v ≠ 0 := by
    intro hz
    have hsub : (U.1 : Set X) ⊆ I.support := by
      intro x hx
      change x ∈ I.support
      rw [Scheme.IdealSheafData.mem_support_iff_of_mem hx, hv, hz,
        Ideal.span_singleton_zero]
      simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe, Submodule.mem_bot,
        forall_eq, Scheme.basicOpen_zero, TopologicalSpace.Opens.mem_bot, not_false_eq_true]
    have hne : (U.1 : Set X).Nonempty := by
      obtain ⟨x⟩ := (inferInstance : Nonempty U.1)
      exact ⟨x.val, x.property⟩
    have hd : Dense (U.1 : Set X) := U.1.isOpen.dense hne
    have hall : (Set.univ : Set X) ⊆ I.support := by
      rw [← hd.closure_eq]
      exact closure_minimal hsub I.support.isClosed
    exact hproper (TopologicalSpace.Closeds.ext (Set.eq_univ_of_univ_subset hall))
  intro a b h
  exact mul_left_cancel₀ hv0 h

#print axioms paired_c3_integral_parameter_regular
end HodgeLean.Foundations.Program.G32Native
