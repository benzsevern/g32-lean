import HodgeLean.Foundations.Program.CyclotomicWeilLinear
import HodgeLean.Adapters.F1575WeilDescent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! Scalar extension of transported determinant carriers. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

theorem s4_determinant_transport_baseChange
    {V W T : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    [AddCommGroup W] [Module ℚ W] [AddCommGroup T] [Module ℚ T]
    {m h : ℕ} (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m))
    (c : (⋀[ℚ]^h V) →ₗ[ℚ] W) (f : W →ₗ[ℚ] T) :
    (((cyc_wedges e).map c).map f).baseChange ℂ =
      ⨆ t : cyc_Field m →ₐ[ℚ] ℂ, (cyc_line e t).map
        (f.baseChange ℂ ∘ₗ c.baseChange ℂ ∘ₗ
          (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) h).symm.toLinearMap) := by
  let E := HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) h
  have hd := cyc_descent_eq e
  have hw : (cyc_wedges e).baseChange ℂ = (cyc_topLines e).map E.symm.toLinearMap := by
    rw [← hd]
    ext x
    rw [Submodule.mem_map_equiv, Submodule.mem_map_equiv]
    change x ∈ (cyc_wedges e).baseChange ℂ ↔ E.symm (E x) ∈ (cyc_wedges e).baseChange ℂ
    rw [LinearEquiv.symm_apply_apply]
  rw [HodgeLean.Adapters.f1575_baseChange_map, HodgeLean.Adapters.f1575_baseChange_map, hw]
  simp only [cyc_topLines, Submodule.map_iSup, ← Submodule.map_comp]
  rfl

end HodgeLean.Foundations.Program
