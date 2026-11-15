import HodgeLean.Foundations.Program.UniversalFamilyB60cRationalChart
import HodgeLean.Foundations.Program.UniversalFamilyB60cFibrePolarization

noncomputable section
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
/-- A rational polarized action marking acquires a Hodge-compatible period coordinate. -/
theorem b60c_period_of_rational_marking (P : g32t_Sixfold) (hP : g32t_IsMember P)
    (υ : g32m_Domain) (e₀ : HQ (b60b_univ υ).X 1 ≃ₗ[ℚ] HQ P.X 1)
    (hJ₀ : ∀ x, e₀ ((b60b_univ υ).W.J x) = P.W.J (e₀ x))
    (hpol₀ : exteriorPower.map 2 e₀.toLinearMap
      (polarizationVec (torusCohomology_cupProductOf (b60b_univ υ).X) (b60b_univ υ).pol) =
      polarizationVec (torusCohomology_cupProductOf P.X) P.pol) :
    ∃ τ : g32m_Domain, ∃ e : HQ (b60b_univ τ).X 1 ≃ₗ[ℚ] HQ P.X 1,
      (∀ x, e ((b60b_univ τ).W.J x) = P.W.J (e x)) ∧
      (b60c_F (b60b_univ τ)).map (e.toLinearMap.baseChange ℂ) = b60c_F P ∧
      exteriorPower.map 2 e.toLinearMap
        (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).pol) =
        polarizationVec (torusCohomology_cupProductOf P.X) P.pol := by
  let e₀C := LinearEquiv.baseChange ℚ ℂ _ _ e₀
  let g := (b60b_homologyCohomologyEquiv υ).trans e₀C
  have hJ : ∀ x, g (b60_omegaC x) = -(P.W.J.baseChange ℂ) (g x) := by
    intro x
    change e₀C (b60b_homologyCohomologyEquiv υ (b60_omegaC x)) = _
    rw [b60b_homologyCohomology_intertwines]
    change e₀C (-((b60b_univ υ).W.J.baseChange ℂ)
      (b60b_homologyCohomologyEquiv υ x)) = _
    rw [map_neg]
    exact congrArg Neg.neg (b60c_complex_action_intertwines (b60b_univ υ) P e₀ hJ₀ _)
  have hE : ∀ x y, (polarizationForm (torusCohomology_cupProductOf P.X)
      hP.nondegenerate).baseChange ℂ (g x) (g y) = b60_E.baseChange ℂ x y := by
    intro x y
    exact (b60c_complex_polarization_isometry (b60b_univ υ) P (b60b_member υ) hP
      e₀ hpol₀ _ _).trans (b60c_homologyCohomology_form υ x y)
  have hsigma : ∀ x, g (b2_conj b60_Lattice x) = HodgeBlocks.sigmaQ _ (g x) := by
    intro x
    change e₀C (b60b_homologyCohomologyEquiv υ (b2_conj b60_Lattice x)) = _
    rw [b60c_homologyCohomology_conj]
    exact (HodgeBlocks.sigmaQ_baseChange e₀.toLinearMap _).symm
  obtain ⟨τ, hτ⟩ := b60c_chart_of_complex_marking P hP g hJ hE hsigma
  let e := (b60c_fibreMarking τ υ).trans e₀
  refine ⟨τ, e, ?_, ?_, ?_⟩
  · intro x
    change e₀ (b60c_fibreMarking τ υ ((b60b_univ τ).W.J x)) = _
    rw [b60c_fibreMarking_action, hJ₀]
    rfl
  · have hcomp : e.toLinearMap.baseChange ℂ ∘ₗ
        (b60b_homologyCohomologyEquiv τ).toLinearMap = g.toLinearMap := by
      apply LinearMap.ext
      intro x
      change (LinearEquiv.baseChange ℚ ℂ _ _
        ((b60c_fibreMarking τ υ).trans e₀)) (b60b_homologyCohomologyEquiv τ x) = _
      rw [LinearEquiv.baseChange_trans]
      change e₀C ((LinearEquiv.baseChange ℚ ℂ _ _ (b60c_fibreMarking τ υ))
        (b60b_homologyCohomologyEquiv τ x)) = e₀C (b60b_homologyCohomologyEquiv υ x)
      exact congrArg e₀C (b60c_fibreMarking_comparison τ υ x)
    have hF : (b60_F τ).map (b60b_homologyCohomologyEquiv τ).toLinearMap =
        b60c_F (b60b_univ τ) := b60b_homologyCohomology_F τ
    calc
      _ = ((b60_F τ).map (b60b_homologyCohomologyEquiv τ).toLinearMap).map
          (e.toLinearMap.baseChange ℂ) := congrArg (Submodule.map _) hF.symm
      _ = (b60_F τ).map (e.toLinearMap.baseChange ℂ ∘ₗ
          (b60b_homologyCohomologyEquiv τ).toLinearMap) :=
        (Submodule.map_comp _ _ _).symm
      _ = b60c_F P := by rw [hcomp]; exact hτ
  · change exteriorPower.map 2 (e₀.toLinearMap ∘ₗ (b60c_fibreMarking τ υ).toLinearMap)
      (polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X)
        (b60b_univ τ).pol) = _
    rw [exteriorPower.map_comp, LinearMap.comp_apply, b60c_fibreMarking_polarization]
    exact hpol₀

#print axioms b60c_period_of_rational_marking

end HodgeLean.Foundations.Program
