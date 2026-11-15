import HodgeLean.Foundations.Program.G32Native.PairedConormalQuotientKernel
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The supplied quotient dual and the prescribed evaluation kernel -/
noncomputable section
set_option maxHeartbeats 200000
open Module
namespace HodgeLean.Foundations.Program.G32Native

/-- The dual image of a quotient by the actual relation line is the prescribed
bilinear evaluation kernel in the exact ordered coordinates. -/
theorem conormal_quotient_dual_range_iff (k : ℕ)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (π : (ℂ × (Fin k → ℂ)) →ₗ[ℂ] W)
    (v : ℂ × (Fin k → ℂ))
    (hker : LinearMap.ker π = Submodule.span ℂ {v})
    (w : ℂ × (Fin k → ℂ)) :
    conormalModelDualCoordinates k w ∈ LinearMap.range π.dualMap ↔
      EulerModel.homogeneousNormalEvaluation k v w = 0 := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, hker]
  have hspan : conormalModelDualCoordinates k w ∈ (Submodule.span ℂ {v}).dualAnnihilator ↔
      conormalModelDualCoordinates k w v = 0 := by
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro h
      exact h v (Submodule.subset_span (Set.mem_singleton v))
    · intro h u hu
      have hs : Submodule.span ℂ {v} ≤ LinearMap.ker (conormalModelDualCoordinates k w) :=
        (Submodule.span_singleton_le_iff_mem v _).mpr h
      exact hs hu
  rw [hspan, conormal_model_dual_evaluation,
    conormal_model_evaluation_dotProduct, conormal_model_evaluation_dotProduct,
    dotProduct_comm]

/-- The actual quotient dual is linearly equivalent to its prescribed
homogeneous evaluation kernel through the exact ordered dual coordinates. -/
def conormalQuotientDualKernelEquiv (k : ℕ)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (π : (ℂ × (Fin k → ℂ)) →ₗ[ℂ] W) (hπ : Function.Surjective π)
    (v : ℂ × (Fin k → ℂ))
    (hker : LinearMap.ker π = Submodule.span ℂ {v}) :
    Dual ℂ W ≃ₗ[ℂ] LinearMap.ker (EulerModel.homogeneousNormalEvaluation k v) := by
  let e := conormalModelDualCoordinates k
  let F : Dual ℂ W →ₗ[ℂ] (ℂ × (Fin k → ℂ)) := e.symm.toLinearMap.comp π.dualMap
  have hF : ∀ ψ, F ψ ∈ LinearMap.ker (EulerModel.homogeneousNormalEvaluation k v) := by
    intro ψ
    apply (conormal_quotient_dual_range_iff k π v hker (F ψ)).mp
    change e (e.symm (π.dualMap ψ)) ∈ LinearMap.range π.dualMap
    rw [LinearEquiv.apply_symm_apply]
    exact LinearMap.mem_range_self π.dualMap ψ
  let f := F.codRestrict (LinearMap.ker (EulerModel.homogeneousNormalEvaluation k v)) hF
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    apply LinearMap.dualMap_injective_of_surjective hπ
    apply e.symm.injective
    exact congrArg Subtype.val hab
  · intro w
    obtain ⟨ψ, hψ⟩ :=
      (conormal_quotient_dual_range_iff k π v hker w.val).mpr w.property
    refine ⟨ψ, Subtype.ext ?_⟩
    change e.symm (π.dualMap ψ) = w.val
    rw [hψ, LinearEquiv.symm_apply_apply]

end HodgeLean.Foundations.Program.G32Native
