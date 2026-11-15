import HodgeLean.Blocks.Weil.RationalKernel
import HodgeLean.Foundations.HodgeLieAlgebra

/-! # Scalar descent of the two Weil determinant lines

The sum of the two top eigenspace ranges is defined over the rationals:
it is the kernel of the rational quadratic exterior-derivation operator.
This identifies it with the complex span of the actual rational Weil classes,
rather than only proving that rational Weil classes map into the two lines.
-/

noncomputable section
open scoped TensorProduct

namespace HodgeLean.Adapters

/-- Scalar extension commutes with the image of a rational linear map. -/
theorem f1575_baseChange_map {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (P : Submodule ℚ V) (f : V →ₗ[ℚ] W) :
    (P.map f).baseChange ℂ = (P.baseChange ℂ).map (f.baseChange ℂ) := by
  rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨1 ⊗ₜ[ℚ] v, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨f v, ⟨v, hv, rfl⟩, rfl⟩

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
  {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ}

/-- Extending the rational Weil-class space recovers both top eigenspace ranges.
This follows from the rational quadratic kernel identity and exact base change. -/
theorem weilClasses_baseChange_eq_topLines (A : HodgeBlocks.WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d) :
    let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
    ((A.weilClasses hH hW).baseChange ℂ).map
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) (k + k)).toLinearMap =
      LinearMap.range (exteriorPower.map (k + k) A.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map (k + k) A.Vsbar.subtype) := by
  dsimp only
  rw [A.weilClasses_eq_ker_derivationKernelOperatorQ hH hW hd,
    ← Foundations.ker_baseChange_eq, ← A.ker_derivationKernelOperator_eq_sup hH hW hd]
  let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  let e := HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) (k + k)
  ext v
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
  have he := LinearMap.congr_fun
    (A.exteriorPowerBaseChangeEquiv_derivationKernelOperatorQ k) (e.symm v)
  change e ((HodgeBlocks.WeilAction.derivationKernelOperatorQ A k).baseChange ℂ
    (e.symm v)) = HodgeBlocks.WeilAction.derivationKernelOperator A k (e (e.symm v)) at he
  rw [e.apply_symm_apply] at he
  constructor
  · intro h
    change (HodgeBlocks.WeilAction.derivationKernelOperatorQ A k).baseChange ℂ
      (e.symm v) = 0 at h
    rw [h, map_zero] at he
    exact he.symm
  · intro h
    apply e.injective
    rw [he, h, map_zero]

end HodgeLean.Adapters
