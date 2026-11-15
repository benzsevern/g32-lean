import HodgeLean.Foundations.Program.UniversalFamilyB60cPeriod
import HodgeLean.Foundations.Program.UniversalFamilyB60cFiltration

noncomputable section
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The marked homology-to-cohomology map factors through the fixed lattice dual. -/
theorem b60c_homologyCohomology_fixed (τ : g32m_Domain) (x : ℂ ⊗[ℤ] b60_Lattice) :
    b60b_homologyCohomologyEquiv τ x =
      (LinearEquiv.baseChange ℚ ℂ _ _ (b60_cohomologyEquiv τ))
        (b2bpol_musical b60_Lattice b60_E x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c u =>
    change (LinearEquiv.baseChange ℚ ℂ _ _ (b60b_periodLinearEquiv (b60b_model τ))).symm
        (b2bpol_musical (b2_abelianLattice (b60b_model τ)) (b60b_form τ)
          ((LinearEquiv.baseChange ℤ ℂ _ _ (b60b_marking τ).toIntLinearEquiv) (c ⊗ₜ u))) = _
    rw [LinearEquiv.baseChange_tmul, b2bpol_musical_tmul, b2bpol_musical_tmul,
      LinearEquiv.baseChange_tmul]
    change c ⊗ₜ[ℚ] (b60b_periodLinearEquiv (b60b_model τ)).symm
        (b2b_flat _ (b60b_form τ) ((1 : ℚ) ⊗ₜ (b60b_marking τ u))) =
      c ⊗ₜ[ℚ] (b60b_periodLinearEquiv (b60b_model τ)).symm
        (b60_markedDualEquiv τ (b2b_flat b60_Lattice b60_E ((1 : ℚ) ⊗ₜ u)))
    congr 2
    ext l
    simp [b60_markedDualEquiv, b2b_flat, b60b_form, b4b_transportForm]

#print axioms b60c_homologyCohomology_fixed

/-- Complexification of the fixed-dual polarization isometry. -/
theorem b60c_cohomologyEquiv_form_complex (τ : g32m_Domain)
    (x y : ℂ ⊗[ℚ] b2b_dual b60_Lattice) :
    (polarizationForm (torusCohomology_cupProductOf (b60b_model τ))
      (b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ)
        (b60b_form_riemann τ))).baseChange ℂ
      ((LinearEquiv.baseChange ℚ ℂ _ _ (b60_cohomologyEquiv τ)) x)
      ((LinearEquiv.baseChange ℚ ℂ _ _ (b60_cohomologyEquiv τ)) y) =
      (b2b_dualForm b60_Lattice b60_E).baseChange ℂ x y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul c x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul d y =>
      simp only [LinearEquiv.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
        b60_cohomologyEquiv_form]

#print axioms b60c_cohomologyEquiv_form_complex

/-- The marked comparison carries the lattice Riemann form to the cohomological form. -/
theorem b60c_homologyCohomology_form (τ : g32m_Domain)
    (x y : ℂ ⊗[ℤ] b60_Lattice) :
    (polarizationForm (torusCohomology_cupProductOf (b60b_model τ))
      (b2_abelian_nondegenerate (b60b_model τ) (b60b_form τ)
        (b60b_form_riemann τ))).baseChange ℂ
      (b60b_homologyCohomologyEquiv τ x) (b60b_homologyCohomologyEquiv τ y) =
      b60_E.baseChange ℂ x y := by
  rw [b60c_homologyCohomology_fixed, b60c_homologyCohomology_fixed,
    b60c_cohomologyEquiv_form_complex]
  exact b2bpol_dualForm_musical b60_Lattice b60_E (b60_flat_bijective τ) x y

#print axioms b60c_homologyCohomology_form

end HodgeLean.Foundations.Program
