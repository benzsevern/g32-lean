import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.TensorProduct.Tower

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
open TensorProduct

namespace HodgeLean.Foundations.Program

/-- Flatness of a composite descends across a faithfully flat second algebra map. -/
theorem s2t_flat_of_flat_faithfullyFlat {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro M N _ _ _ _ f hf
  let fs : S ⊗[R] M →ₗ[S] S ⊗[R] N := AlgebraTensorModule.lTensor S S f
  change Function.Injective fs
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective S T fs]
  let eM := AlgebraTensorModule.cancelBaseChange R S S T M
  let eN := AlgebraTensorModule.cancelBaseChange R S S T N
  have heq : (AlgebraTensorModule.lTensor S T f).comp eM.toLinearMap =
      eN.toLinearMap.comp (AlgebraTensorModule.lTensor S T fs) := by
    exact AlgebraTensorModule.lTensor_comp_cancelBaseChange R S S f
  have hi : Function.Injective ((AlgebraTensorModule.lTensor S T f).comp eM.toLinearMap) :=
    (Module.Flat.lTensor_preserves_injective_linearMap f hf).comp eM.injective
  rw [heq] at hi
  intro x y hxy
  apply hi
  exact congrArg eN hxy

end HodgeLean.Foundations.Program
