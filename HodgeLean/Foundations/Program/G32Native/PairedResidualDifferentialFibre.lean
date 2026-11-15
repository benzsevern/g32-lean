import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The original differential pullback on field fibres -/
noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual absolute differential pullback after evaluating in a common field.
Source: Hartshorne, Algebraic Geometry, II.8. -/
def residualDifferentialFibreMap
    (R S T K : Type*) [CommRing R] [CommRing S] [CommRing T] [Field K]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra R K] [Algebra S K] [Algebra T K]
    [IsScalarTower R S K] [IsScalarTower R T K] [IsScalarTower S T K] :
    K ⊗[S] Ω[S⁄R] →ₗ[K] K ⊗[T] Ω[T⁄R] :=
  (((TensorProduct.mk T K Ω[T⁄R] 1).restrictScalars S).comp
    (KaehlerDifferential.map R R S T)).liftBaseChange K

/-- The fibre pullback retains the differential of every original element.
Source: Hartshorne, Algebraic Geometry, II.8. -/
theorem residual_differential_fibre_map_D
    (R S T K : Type*) [CommRing R] [CommRing S] [CommRing T] [Field K]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra R K] [Algebra S K] [Algebra T K]
    [IsScalarTower R S K] [IsScalarTower R T K] [IsScalarTower S T K] (a : S) :
    residualDifferentialFibreMap R S T K (1 ⊗ₜ[S] KaehlerDifferential.D R S a) =
      1 ⊗ₜ[T] KaehlerDifferential.D R T (algebraMap S T a) := by
  simp only [residualDifferentialFibreMap, LinearMap.liftBaseChange_one_tmul,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, KaehlerDifferential.map_D]
  rfl

#print axioms residualDifferentialFibreMap
#print axioms residual_differential_fibre_map_D
end HodgeLean.Foundations.Program.G32Native
