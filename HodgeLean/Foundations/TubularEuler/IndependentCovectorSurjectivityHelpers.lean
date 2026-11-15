import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! # Surjectivity from independent coordinate covectors

HC no distance; AV milestone no distance. -/

noncomputable section
namespace HodgeLean.Foundations.TubularEuler

theorem independent_covectors_surjective
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    {ι : Type*} [Fintype ι] (f : ι → E →ₗ[K] K)
    (hf : LinearIndependent K f) :
    Function.Surjective (LinearMap.pi f) := by
  classical
  let b := (Pi.basisFun K ι).dualBasis
  have heq : (LinearMap.pi f).dualMap = b.constr K f := by
    apply b.ext
    intro i
    ext v
    simp [b, Pi.single_apply]
  apply LinearMap.dualMap_injective_iff.mp
  rw [heq]
  exact b.injective_constr_of_linearIndependent hf

#print axioms independent_covectors_surjective

theorem independent_continuous_covectors_surjective
    {K E : Type*} [NontriviallyNormedField K] [NormedAddCommGroup E] [NormedSpace K E]
    {ι : Type*} [Fintype ι] (f : ι → E →L[K] K)
    (hf : LinearIndependent K f) :
    Function.Surjective (fun v => fun i => f i v) := by
  have hi : Function.Injective (ContinuousLinearMap.coeLM K :
      (E →L[K] K) →ₗ[K] E →ₗ[K] K) := by
    intro a b h
    exact ContinuousLinearMap.ext fun v => LinearMap.congr_fun h v
  exact independent_covectors_surjective (fun i => (f i).toLinearMap)
    (hf.map' (ContinuousLinearMap.coeLM K) (LinearMap.ker_eq_bot.mpr hi))

#print axioms independent_continuous_covectors_surjective

end HodgeLean.Foundations.TubularEuler
