import HodgeLean.Foundations.Program.UniversalFamilyB60cComparison

noncomputable section
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The homology comparison respects the real structures. -/
theorem b60c_homologyCohomology_conj (τ : g32m_Domain) (x : ℂ ⊗[ℤ] b60_Lattice) :
    b60b_homologyCohomologyEquiv τ (b2_conj b60_Lattice x) =
      HodgeBlocks.sigmaQ _ (b60b_homologyCohomologyEquiv τ x) := by
  rw [b60c_homologyCohomology_fixed, b60c_homologyCohomology_fixed]
  change (b60_cohomologyEquiv τ).toLinearMap.baseChange ℂ
      (b2bpol_musical b60_Lattice b60_E (b2_conj b60_Lattice x)) =
    HodgeBlocks.sigmaQ _ ((b60_cohomologyEquiv τ).toLinearMap.baseChange ℂ
      (b2bpol_musical b60_Lattice b60_E x))
  rw [HodgeBlocks.sigmaQ_baseChange, b2bpol_sigma_musical]

#print axioms b60c_homologyCohomology_conj

/-- The fixed rational dual lattice identifies the rational cohomology of two fibres. -/
def b60c_fibreMarking (τ υ : g32m_Domain) :
    HQ (b60b_univ τ).X 1 ≃ₗ[ℚ] HQ (b60b_univ υ).X 1 :=
  (b60_cohomologyEquiv τ).symm.trans (b60_cohomologyEquiv υ)

/-- The rational fibre marking agrees with the common complex homology marking. -/
theorem b60c_fibreMarking_comparison (τ υ : g32m_Domain) (x : ℂ ⊗[ℤ] b60_Lattice) :
    (LinearEquiv.baseChange ℚ ℂ _ _ (b60c_fibreMarking τ υ))
        (b60b_homologyCohomologyEquiv τ x) = b60b_homologyCohomologyEquiv υ x := by
  rw [b60c_homologyCohomology_fixed, b60c_homologyCohomology_fixed]
  change (LinearEquiv.baseChange ℚ ℂ _ _
    ((b60_cohomologyEquiv τ).symm.trans (b60_cohomologyEquiv υ)))
    ((LinearEquiv.baseChange ℚ ℂ _ _ (b60_cohomologyEquiv τ))
      (b2bpol_musical b60_Lattice b60_E x)) = _
  simp only [LinearEquiv.baseChange_trans,
    LinearEquiv.baseChange_symm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

#print axioms b60c_fibreMarking_comparison

end HodgeLean.Foundations.Program
