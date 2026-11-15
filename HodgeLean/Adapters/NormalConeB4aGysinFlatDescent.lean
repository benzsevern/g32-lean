import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.TensorProduct.Tower

noncomputable section
namespace HodgeLean.Adapters
open TensorProduct

/-- Flatness over a base descends through a faithfully flat extension of
its source algebra. -/
theorem a3b4a_gysin_flat_of_faithfullyFlat_source
    {A S T : Type*} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]
    [Module.FaithfullyFlat S T] [Module.Flat A T] : Module.Flat A S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  let fS := f.baseChange S
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective S T fS).mp
  let eN := AlgebraTensorModule.cancelBaseChange A S T T N
  let eP := AlgebraTensorModule.cancelBaseChange A S T T P
  have heq : LinearMap.lTensor T fS =
      (eP.symm.toLinearMap.restrictScalars S) ∘ₗ
        ((f.baseChange T).restrictScalars S) ∘ₗ
          (eN.toLinearMap.restrictScalars S) := by
    apply TensorProduct.ext'
    intro t y
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | tmul s n =>
      change _ = _
      simp only [fS, eN, eP, LinearMap.lTensor_tmul, LinearMap.baseChange_tmul,
      LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
      AlgebraTensorModule.cancelBaseChange_tmul, AlgebraTensorModule.cancelBaseChange_symm_tmul,
        TensorProduct.smul_tmul', TensorProduct.smul_tmul, one_smul, smul_eq_mul, mul_one]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  rw [heq]
  exact eP.symm.injective.comp
    ((Module.Flat.lTensor_preserves_injective_linearMap (M := T) f hf).comp eN.injective)

end HodgeLean.Adapters
