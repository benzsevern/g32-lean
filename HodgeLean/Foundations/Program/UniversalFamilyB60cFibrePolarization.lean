import HodgeLean.Foundations.Program.UniversalFamilyB60cFibreMarking

noncomputable section
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Rational fibre markings intertwine the quadratic actions. -/
theorem b60c_fibreMarking_action (τ υ : g32m_Domain) (x : HQ (b60b_univ τ).X 1) :
    b60c_fibreMarking τ υ ((b60b_univ τ).W.J x) =
      (b60b_univ υ).W.J (b60c_fibreMarking τ υ x) := by
  obtain ⟨u, rfl⟩ := (b60_cohomologyEquiv τ).surjective x
  change b60_cohomologyEquiv υ ((b60_cohomologyEquiv τ).symm
      ((b60_cohomAction τ).1 (b60_cohomologyEquiv τ u))) =
    (b60_cohomAction υ).1 (b60_cohomologyEquiv υ
      ((b60_cohomologyEquiv τ).symm (b60_cohomologyEquiv τ u)))
  rw [← b60_cohomologyEquiv_action, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply, b60_cohomologyEquiv_action]

#print axioms b60c_fibreMarking_action

/-- Rational fibre markings preserve the given polarization bivectors. -/
theorem b60c_fibreMarking_polarization (τ υ : g32m_Domain) :
    exteriorPower.map 2 (b60c_fibreMarking τ υ).toLinearMap
      (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).pol) =
      polarizationVec (torusCohomology_cupProductOf (b60b_univ υ).X) (b60b_univ υ).pol := by
  letI := (torusCohomology_cupProductOf (b60b_univ τ).X).finite
  letI := (torusCohomology_cupProductOf (b60b_univ υ).X).finite
  apply b60c_bivector_map_of_dualForm _ (b60b_member τ).nondegenerate
    (b60b_member υ).nondegenerate
  intro x y
  obtain ⟨u, rfl⟩ := (b60_cohomologyEquiv τ).surjective x
  obtain ⟨v, rfl⟩ := (b60_cohomologyEquiv τ).surjective y
  change polarizationForm (torusCohomology_cupProductOf (b60b_model υ))
      (b60b_member υ).nondegenerate
      (b60_cohomologyEquiv υ ((b60_cohomologyEquiv τ).symm (b60_cohomologyEquiv τ u)))
      (b60_cohomologyEquiv υ ((b60_cohomologyEquiv τ).symm (b60_cohomologyEquiv τ v))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact (b60_cohomologyEquiv_form υ u v).trans (b60_cohomologyEquiv_form τ u v).symm

#print axioms b60c_fibreMarking_polarization

end HodgeLean.Foundations.Program
