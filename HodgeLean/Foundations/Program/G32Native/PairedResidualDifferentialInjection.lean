import HodgeLean.Foundations.Program.G32Native.PairedResidualDifferentialFibre

/-! # Actual cotangent fibre injections detected by tangent lifting -/
noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- Lifting all tangent derivations forces injectivity of the original
cotangent pullback on the same field fibre.
Source: Hartshorne, Algebraic Geometry, II.8; duality of vector spaces. -/
theorem residual_differential_fibre_injective_of_tangent_lift
    (R S T K : Type*) [CommRing R] [CommRing S] [CommRing T] [Field K]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra R K] [Algebra S K] [Algebra T K]
    [IsScalarTower R S K] [IsScalarTower R T K] [IsScalarTower S T K]
    (h : ∀ E : Derivation R S K, ∃ D : Derivation R T K,
      ∀ a, D (algebraMap S T a) = E a) :
    Function.Injective (residualDifferentialFibreMap R S T K) := by
  apply LinearMap.dualMap_surjective_iff.mp
  intro L
  let E : Derivation R S K := (KaehlerDifferential.linearMapEquivDerivation (R := R) (S := S) (M := K))
    ((LinearMap.liftBaseChangeEquiv K).symm L)
  obtain ⟨D, hD⟩ := h E
  refine ⟨D.liftKaehlerDifferential.liftBaseChange K, ?_⟩
  apply (LinearMap.liftBaseChangeEquiv K).symm.injective
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  change D.liftKaehlerDifferential.liftBaseChange K
    (residualDifferentialFibreMap R S T K (1 ⊗ₜ[S] KaehlerDifferential.D R S a)) =
      L (1 ⊗ₜ[S] KaehlerDifferential.D R S a)
  rw [residual_differential_fibre_map_D, LinearMap.liftBaseChange_one_tmul,
    Derivation.liftKaehlerDifferential_comp_D]
  exact hD a

#print axioms residual_differential_fibre_injective_of_tangent_lift
end HodgeLean.Foundations.Program.G32Native
