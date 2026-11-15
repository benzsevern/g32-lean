import HodgeLean.Blocks.Weil.DiagonalKernel

/-! # The rational Weil kernel operator has no nilpotent zero part -/

open scoped TensorProduct
noncomputable section

namespace HodgeBlocks.WeilAction

/-- The rational Weil operator has no generalized zero vectors outside its kernel. -/
theorem derivationKernelOperatorQ_no_nilpotent
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {M : QHodgeStructure 1 V} {d : ℚ} (A : WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d) :
    let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
    ∀ x, derivationKernelOperatorQ A k (derivationKernelOperatorQ A k x) = 0 →
      derivationKernelOperatorQ A k x = 0 := by
  dsimp only
  let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  let n := k + k
  have hVs : Module.finrank ℂ ↥A.Vs = n := by
    simpa [k, n] using A.finrank_Vs_eq_twice_inf_H10 hH hW
  have hVsbar : Module.finrank ℂ ↥A.Vsbar = n := by
    rw [A.finrank_Vsbar_eq_Vs, hVs]
  obtain ⟨b, hb⟩ := A.exists_adapted_Jc_basis hd n hVs hVsbar
  have hdiag : ∀ s, ∃ c : ℂ,
      derivationKernelOperator A k (b.exteriorPower n s) = c • b.exteriorPower n s := by
    intro s
    exact ⟨_, A.derivationKernelOperator_adapted_exterior_basis hd k b hb s⟩
  choose c hc using hdiag
  intro x hx
  apply complexifyWedge_injective n
  rw [A.complexifyWedge_derivationKernelOperatorQ k, map_zero]
  apply apply_eq_zero_of_apply_apply_eq_zero_of_basis
    (b.exteriorPower n) (derivationKernelOperator A k) c hc
  rw [← A.complexifyWedge_derivationKernelOperatorQ k,
    ← A.complexifyWedge_derivationKernelOperatorQ k, hx, map_zero]

#print axioms derivationKernelOperatorQ_no_nilpotent

end HodgeBlocks.WeilAction
