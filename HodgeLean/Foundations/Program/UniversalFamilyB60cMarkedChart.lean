import HodgeLean.Foundations.Program.UniversalFamilyB60cComplexMarking

noncomputable section
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- An action-compatible real isometry gives a member's Hodge plane a fixed period coordinate. -/
theorem b60c_chart_of_complex_marking (P : g32t_Sixfold) (hP : g32t_IsMember P)
    (g : (ℂ ⊗[ℤ] b60_Lattice) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ P.X 1))
    (hJ : ∀ x, g (b60_omegaC x) = -(P.W.J.baseChange ℂ) (g x))
    (hE : ∀ x y, (polarizationForm (torusCohomology_cupProductOf P.X)
      hP.nondegenerate).baseChange ℂ (g x) (g y) = b60_E.baseChange ℂ x y)
    (hsigma : ∀ x, g (b2_conj b60_Lattice x) = HodgeBlocks.sigmaQ _ (g x)) :
    ∃ τ : g32m_Domain, (b60_F τ).map g.toLinearMap = b60c_F P := by
  letI := (torusCohomology_cupProductOf P.X).finite
  let F := (b60c_F P).comap g.toLinearMap
  have hm : F.map g.toLinearMap = b60c_F P :=
    Submodule.map_comap_eq_of_surjective g.surjective _
  have hd := b60c_member_hodge_dimensions P hP
  have hn : (Module.End.eigenspace b60_omegaC
      (-Complex.I * (Real.sqrt 3 : ℂ))).map g.toLinearMap = P.W.Vs := by
    simpa [HodgeBlocks.WeilAction.Vs, HodgeBlocks.WeilAction.omegaC, neg_mul] using
      b60c_marking_eigenspaces P g hJ (Complex.I * (Real.sqrt 3 : ℂ))
  have hp : (Module.End.eigenspace b60_omegaC
      (Complex.I * (Real.sqrt 3 : ℂ))).map g.toLinearMap = P.W.Vsbar := by
    simpa [HodgeBlocks.WeilAction.Vsbar, HodgeBlocks.WeilAction.omegaC, neg_mul] using
      b60c_marking_eigenspaces P g hJ (-(Complex.I * (Real.sqrt 3 : ℂ)))
  have hdim : Module.finrank ℂ F = 6 := by
    rw [← g.finrank_map_eq F, hm]
    exact hd.1
  have hneg : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace b60_omegaC
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
    rw [← g.finrank_map_eq _, Submodule.map_inf _ g.injective, hm, hn, inf_comm]
    exact hd.2.1
  have hpos : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace b60_omegaC
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
    rw [← g.finrank_map_eq _, Submodule.map_inf _ g.injective, hm, hp, inf_comm]
    exact hd.2.2
  obtain ⟨τ, hτ⟩ := b60c_fixed_filtration_chart F hdim hneg hpos
    (b60c_member_riemann_pullback P hP g hE hsigma)
  exact ⟨τ, hτ ▸ hm⟩

#print axioms b60c_chart_of_complex_marking

end HodgeLean.Foundations.Program
