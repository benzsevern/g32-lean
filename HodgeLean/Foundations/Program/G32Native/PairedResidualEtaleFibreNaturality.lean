import HodgeLean.Foundations.Program.G32Native.PairedResidualEtaleFibre

/-! # Naturality of the original differential fibre under localization -/
noncomputable section
set_option maxHeartbeats 400000
open KaehlerDifferential TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- The original section differential and its formally etale localization
agree under the actual differential fibre identification.
Source: Hartshorne, Algebraic Geometry, II.8. -/
theorem residual_etale_differential_fibre_naturality
    (R S A L K : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing L] [Field K]
    [Algebra R S] [Algebra R A] [Algebra R L] [Algebra R K]
    [Algebra S A] [Algebra S L] [Algebra S K]
    [Algebra A L] [Algebra A K] [Algebra L K]
    [IsScalarTower R S A] [IsScalarTower R S L] [IsScalarTower R S K]
    [IsScalarTower R A L] [IsScalarTower R A K] [IsScalarTower R L K]
    [IsScalarTower S A L] [IsScalarTower S A K] [IsScalarTower S L K]
    [IsScalarTower A L K] [Algebra.FormallyEtale A L] :
    (residualEtaleDifferentialFibreEquiv R A L K).toLinearMap.comp
      (residualDifferentialFibreMap R S L K) = residualDifferentialFibreMap R S A K := by
  ext a
  change residualEtaleDifferentialFibreEquiv R A L K
    (residualDifferentialFibreMap R S L K (1 ⊗ₜ[S] D R S a)) =
      residualDifferentialFibreMap R S A K (1 ⊗ₜ[S] D R S a)
  rw [residual_differential_fibre_map_D, IsScalarTower.algebraMap_apply S A L,
    residual_etale_differential_fibre_D, residual_differential_fibre_map_D]

#print axioms residual_etale_differential_fibre_naturality
end HodgeLean.Foundations.Program.G32Native
