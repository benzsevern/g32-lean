import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.TensorProduct.Tower

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open TensorProduct
namespace HodgeLean.Foundations.Program

/-- Flatness over the scalar ring descends from a faithfully flat extension of the target algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 2.5.1. -/
theorem s2e_flat_of_faithfullyFlat_extension
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat R T] [Module.FaithfullyFlat S T] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  change Function.Injective (f.baseChange S)
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective S T]
  change Function.Injective ((f.baseChange S).baseChange T)
  let EN := AlgebraTensorModule.cancelBaseChange R S T T N
  let EP := AlgebraTensorModule.cancelBaseChange R S T T P
  have he : (f.baseChange S).baseChange T =
      EP.symm.toLinearMap.comp ((f.baseChange T).comp EN.toLinearMap) := by
    ext
    simp [EN, EP]
  rw [he]
  exact EP.symm.injective.comp
    ((Module.Flat.lTensor_preserves_injective_linearMap f hf).comp EN.injective)

#print axioms s2e_flat_of_faithfullyFlat_extension
end HodgeLean.Foundations.Program
