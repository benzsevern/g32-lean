import HodgeLean.Foundations.Program.SchoenCycleClassDefs
import HodgeLean.Foundations.Program.SchoenCyclePushDefs
import HodgeLean.Foundations.Program.SchoenCycleC2NormalizedSumHelpers

/-! # Supported basis and dependent witness transport

The coefficients and supported groups retain their specified ambient spaces.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
open scoped BigOperators Manifold ContDiff OnePoint TensorProduct
namespace HodgeLean.WitnessSelection.StageTwo

/-- Coordinates for a specified change of rational basis, in contravariant order.
Source: Bourbaki, Algebra, II, §3, coordinates relative to a basis.
HC no distance; AV milestone no distance. -/
def basisCoefficients {V : Type*} [AddCommGroup V] [Module ℚ V]
    {n m : ℕ} (b c : Module.Basis (Fin n) ℚ V)
    (a : Fin n → Fin m → ℚ) (j : Fin n) (t : Fin m) : ℚ :=
  ∑ i, b.repr (c j) i * a i t

example {V : Type*} [AddCommGroup V] [Module ℚ V] {n m : ℕ}
    (b : Module.Basis (Fin n) ℚ V) (a : Fin n → Fin m → ℚ) :
    basisCoefficients b b a = a := by
  funext j t
  simp [basisCoefficients, Module.Basis.repr_self, Finsupp.single_apply]

/-- The actual cycle after changing the coefficients of the retained component orbit.
Repeated primes are collected by the existing rational orbit construction.
Source: Fulton, Intersection Theory, §1.4.
HC no distance; AV milestone no distance. -/
def changedOrbit {V : Type*} [AddCommGroup V] [Module ℚ V]
    {n m : ℕ} (b c : Module.Basis (Fin n) ℚ V)
    (a : Fin n → Fin m → ℚ) {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (δ : W ⟶ W) (j : Fin n) : AlgebraicCycle W.left ℚ :=
  s2e_rationalOrbitCycle ι δ m (basisCoefficients b c a j)

example {V : Type*} [AddCommGroup V] [Module ℚ V] {n m : ℕ}
    (b c : Module.Basis (Fin n) ℚ V) (a : Fin n → Fin m → ℚ)
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left] (ι : Q ⟶ W) (δ : W ⟶ W) (j) :
    changedOrbit b c a ι δ j =
      s2e_rationalOrbitCycle ι δ m (basisCoefficients b c a j) := rfl

end HodgeLean.WitnessSelection.StageTwo
