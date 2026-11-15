import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CoefficientBaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

noncomputable section
open AlgebraicTopology.Singular
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Extension from rational to complex coefficients is injective on singular homology. -/
theorem s0_qToCHomology_injective (X : TopCat) (n : ℕ) :
    Function.Injective (qToCHomology X n) := by
  letI : Module ℚ ((CChains X).homology n) := Module.compHom _ (algebraMap ℚ ℂ)
  letI : IsScalarTower ℚ ℂ ((CChains X).homology n) := IsScalarTower.of_compHom ℚ ℂ _
  intro x y h
  have he : (1 : ℂ) ⊗ₜ[ℚ] x = (1 : ℂ) ⊗ₜ[ℚ] y := by
    apply (qToCHomology_isBaseChange X n).equiv.injective
    simpa only [IsBaseChange.equiv_tmul, one_smul] using h
  have hz : (1 : ℂ) ⊗ₜ[ℚ] (x - y) = 0 := by
    rw [TensorProduct.tmul_sub, he, sub_self]
  exact sub_eq_zero.mp ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := ℚ) (A := ℂ) ((QChains X).homology n) (x - y)).mp hz)

#print axioms s0_qToCHomology_injective
end HodgeLean.Foundations.Program
