import HodgeLean.Foundations.Program.G32Native.RetainedNormalFramePairing
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Quotients defined by a finite covector frame -/
noncomputable section
set_option maxHeartbeats 100000
namespace HodgeLean.Foundations.TubularEuler

/-- Express evaluation on a covector family in the dual coordinates of a
specified finite basis.
Source: dual evaluation and `Module.Basis.dualBasis.equivFun`. -/
def framedCovectorQuotient {V : Type*} [AddCommGroup V] [Module ℂ V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {k : ℕ} (b : Module.Basis (Fin k) ℂ V)
    (D : V →ₗ[ℂ] (E →L[ℂ] ℂ)) :
    E →L[ℂ] (Fin k → ℂ) :=
  ContinuousLinearMap.pi (fun i => D (b i))

/-- The finite coefficient pairing recovers evaluation of each original
covector, before any geometric module is specialized.
Source: `dual_coordinate_pairing`. -/
theorem framedCovectorQuotient_pairing {V : Type*} [AddCommGroup V] [Module ℂ V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {k : ℕ} (b : Module.Basis (Fin k) ℂ V)
    (D : V →ₗ[ℂ] (E →L[ℂ] ℂ)) (v : E) (a : V) :
    (∑ i, framedCovectorQuotient b D v i * b.repr a i) = D a v := by
  symm
  conv_lhs => rw [← b.sum_repr a]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, framedCovectorQuotient,
    ContinuousLinearMap.pi_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _


#print axioms framedCovectorQuotient_pairing
end HodgeLean.Foundations.TubularEuler
