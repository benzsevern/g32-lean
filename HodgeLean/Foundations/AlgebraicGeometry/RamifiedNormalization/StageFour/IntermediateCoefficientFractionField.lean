import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A faithfully embedded chart coefficient ring between the original ring and its fraction field has that same fraction field. -/
theorem fraction_field_of_intermediate_coefficient_ring
    {R A K : Type*} [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]
    [IsFractionRing R K] [FaithfulSMul A K] : IsFractionRing A K := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective R z
  refine ⟨algebraMap R A x, algebraMap R A y, ?_⟩
  rw [← IsScalarTower.algebraMap_apply R A K x, ← IsScalarTower.algebraMap_apply R A K y]

end AlgebraicGeometry.RamifiedNormalization.StageFour
