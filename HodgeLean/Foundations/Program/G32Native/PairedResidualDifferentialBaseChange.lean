import HodgeLean.Foundations.Program.G32Native.PairedResidualDifferentialFibre
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Comparing the original cotangent fibre with iterated scalar extension -/
noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
open TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- Cancellation of the intermediate tensor factor identifies the original
field-fibre pullback with scalar extension of the actual differential map.
Source: Hartshorne, Algebraic Geometry, II.8. -/
theorem residual_differential_fibre_baseChange
    (R S T K : Type*) [CommRing R] [CommRing S] [CommRing T] [Field K]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra R K] [Algebra S K] [Algebra T K]
    [IsScalarTower R S K] [IsScalarTower R T K] [IsScalarTower S T K] :
    (KaehlerDifferential.mapBaseChange R S T).baseChange K =
      (residualDifferentialFibreMap R S T K).comp
        (AlgebraTensorModule.cancelBaseChange S T K K Ω[S⁄R]).toLinearMap := by
  ext a
  change (1 : K) ⊗ₜ[T]
      (KaehlerDifferential.mapBaseChange R S T (1 ⊗ₜ[S] KaehlerDifferential.D R S a)) =
    residualDifferentialFibreMap R S T K
      ((AlgebraTensorModule.cancelBaseChange S T K K Ω[S⁄R])
        (1 ⊗ₜ[T] (1 ⊗ₜ[S] KaehlerDifferential.D R S a)))
  simp only [KaehlerDifferential.mapBaseChange_tmul, one_smul,
    KaehlerDifferential.map_D, AlgebraTensorModule.cancelBaseChange_tmul,
    residual_differential_fibre_map_D]

#print axioms residual_differential_fibre_baseChange
end HodgeLean.Foundations.Program.G32Native
